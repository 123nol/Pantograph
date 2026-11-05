#!/usr/bin/env python3
"""Native validation controls, including compiler-producing tactics; Mathlib is an explicit separate gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import selectors
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCOPE = "execution-closure-and-representation-aware-audit"
VERSION = 3
MATHLIB_PIN = "29dcec074de168ac2bf835a77ef68bbe069194c5"


class Session:
    def __init__(self, entries, env, imports):
        self.entries = entries
        self.stderr = tempfile.TemporaryFile(mode="w+t")
        self.proc = subprocess.Popen([str(ROOT / ".lake/build/bin/repl"), *imports],
                                     cwd=ROOT, env=env, text=True, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=self.stderr)
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)
        assert self.line() == "ready."
        self.ids = set()
        self.roots = {}

    def __enter__(self):
        return self

    def __exit__(self, kind, value, traceback):
        if self.proc.poll() is None:
            self.proc.kill()
        self.proc.wait(timeout=30)
        self.selector.close()
        self.stderr.close()

    def line(self):
        assert self.selector.select(90), "REPL response deadline exceeded"
        return self.proc.stdout.readline().rstrip("\n")

    def call(self, command, payload):
        request = command + " " + json.dumps(payload, separators=(",", ":"))
        self.proc.stdin.write(request + "\n")
        self.proc.stdin.flush()
        line = self.line()
        response = json.loads(line)
        self.entries.append(dict(command=command, request=payload, request_line=request,
                                 response=response, response_line=line))
        assert "Uncaught IO exception" not in line
        if "stateId" in response:
            self.ids.add(response["stateId"])
            self.roots[response["stateId"]] = response["root"]
        if "nextStateId" in response:
            self.ids.add(response["nextStateId"])
            if command == "goal.tactic":
                assert response["validation"] == dict(version=VERSION, scope=SCOPE, checked=True)
                self.roots[response["nextStateId"]] = self.roots[payload["stateId"]]
            elif command == "goal.continue":
                self.roots[response["nextStateId"]] = self.roots[payload["target"]]
        for unit in response.get("units", []):
            if "goalStateId" in unit:
                self.ids.add(unit["goalStateId"])
                self.roots[unit["goalStateId"]] = unit["goals"][0]["name"] if len(unit["goals"]) == 1 else None
        return response

    def start(self, expression, levels=()):
        response = self.call("goal.start", dict(expr=expression, levels=list(levels)))
        assert "stateId" in response, response
        return response

    def tactic(self, state, text, index=0):
        return self.call("goal.tactic", dict(stateId=state, goalId=index, tactic=text))

    def certify(self, state):
        response = self.call("goal.certify", dict(stateId=state))
        assert response["status"] == "certified" and "receipt" in response, response
        assert response["receipt"]["root"] == self.roots[state] and response["receipt"]["rootType"]
        return response

    def finish(self):
        self.call("goal.delete", dict(stateIds=sorted(self.ids)))
        assert self.call("stat", {}) == dict(nGoals=0)
        self.proc.stdin.close()
        assert self.proc.wait(timeout=30) == 0
        assert self.proc.stdout.read() == ""
        self.stderr.seek(0)
        assert self.stderr.read() == ""


def environment(mathlib):
    paths = [ROOT / ".lake/build/lib", ROOT / ".lake/packages/LSpec/.lake/build/lib"]
    if mathlib:
        assert (ROOT / "lean-toolchain").read_text() == (mathlib / "lean-toolchain").read_text()
        paths += [mathlib / ".lake/build/lib"]
        paths += [package / ".lake/build/lib" for package in (mathlib / ".lake/packages").iterdir()
                  if package.is_dir()]
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    return env


def verify_mathlib_sources(mathlib, reference):
    tree = subprocess.check_output(["git", "-C", str(reference), "ls-tree", "-r", "--full-tree", MATHLIB_PIN], text=True)
    checked, differences, expected = 0, [], set()
    for row in tree.splitlines():
        entry, name = row.split("\t", 1)
        if not (name.endswith(".lean") or name in {"lean-toolchain", "lake-manifest.json"}):
            continue
        expected.add(name)
        path = mathlib / name
        if not path.is_file():
            differences.append(dict(path=name, reason="missing"))
            continue
        data = path.read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != entry.split()[2]:
            differences.append(dict(path=name, reason="different"))
        checked += 1
    extras = [str(path.relative_to(mathlib)) for path in (mathlib / "Mathlib").rglob("*.lean")
              if str(path.relative_to(mathlib)) not in expected]
    assert not differences and not extras, dict(differences=differences, extra_lean_files=extras)
    return dict(reference_commit=MATHLIB_PIN, checked_files=checked, missing_or_different=differences,
                local_extra_lean_files=extras)


def core_gate(env):
    entries = []
    imports = ["Init", "Test.ContractFixtures"]
    with Session(entries, env, imports) as session:
        descriptor = session.call("protocol.describe", {})
        assert descriptor["protocolVersion"] == 3 and descriptor["transitionValidationVersion"] == VERSION
        root = session.start("True")
        done = session.tactic(root["stateId"], "contract_inert_residue")
        assert not done["goals"] and not done["hasSorry"] and not done["hasUnsafe"]
        session.certify(done["nextStateId"])
        inspected = session.call("goal.inspect", dict(stateId=done["nextStateId"], goals=[root["root"]]))
        assert inspected["obligations"][0]["status"] == "complete"
        # Ordinary candidate failures preserve the original retained input.
        failed = session.tactic(root["stateId"], "exact Nat.zero")
        assert "tacticErrors" in failed and "nextStateId" not in failed
        alternate = session.tactic(root["stateId"], "exact True.intro")
        session.certify(alternate["nextStateId"])
        resumed = session.call("goal.continue", dict(target=alternate["nextStateId"], goals=[root["root"]]))
        session.certify(resumed["nextStateId"])
        units = session.call("frontend.process", dict(file="universe u\nexample (α : Sort u) (a : α) : α := by sorry",
                                                       sorrys=True, invocations=False))["units"]
        frontend = next(unit for unit in units if "goalStateId" in unit)
        solved = session.tactic(frontend["goalStateId"], "exact a")
        assert session.certify(solved["nextStateId"])["receipt"]["levels"] == ["u"]
        session.finish()
    compiler_controls(entries, env, imports)
    with Session(entries, env, imports) as session:
        root = session.start("True")
        session.proc.stdin.write('goal.tactic {"stateId":0,"tactic":"contract_invalid_mutation"}\nstat {}\n')
        session.proc.stdin.flush()
        line = session.line()
        error = json.loads(line)
        assert error["error"] == "validation" and "owner=" in error["desc"] and "path=" in error["desc"]
        assert set(error) == {"error", "desc"}
        entries.append(dict(command="goal.tactic", request=dict(stateId=0, tactic="contract_invalid_mutation"),
                            response=error, response_line=line))
        session.proc.stdin.close()
        assert session.proc.wait(timeout=30) != 0
        assert session.proc.stdout.read() == "", "accepted input after integrity failure"
    return entries


def compiler_sequence(session, statement):
    """`unfold Nat.pow` compiles the match splitter; the state must stay usable and certify."""
    root = session.start(statement)
    middle = session.tactic(root["stateId"], "intro m n")
    unfolded = session.tactic(middle["nextStateId"], "unfold Nat.pow")
    assert unfolded["goals"] and not unfolded["hasSorry"] and not unfolded["hasUnsafe"], unfolded
    inspected = session.call("goal.inspect", dict(stateId=unfolded["nextStateId"], goals=[root["root"]]))
    assert inspected["obligations"][0]["status"] != "complete", inspected
    split = session.tactic(unfolded["nextStateId"], "split")
    assert len(split["goals"]) == 2, split
    first = session.tactic(split["nextStateId"], "rfl")
    last = session.tactic(first["nextStateId"], "rfl")
    assert not last["goals"] and not last["hasSorry"] and not last["hasUnsafe"]
    receipt = session.certify(last["nextStateId"])["receipt"]
    assert "_cstage" not in " ".join(receipt["auxiliary"]) and any("splitter" in name for name in receipt["auxiliary"])


def compiler_controls(entries, env, imports):
    statement = "∀ m n : Nat, Nat.pow m n = Nat.pow m n"
    with Session(entries, env, imports) as session:
        compiler_sequence(session, statement)
        session.finish()
    # Warmed history: an earlier simp and a rewrite through generated equations.
    with Session(entries, env, imports) as session:
        warm = session.start("True ∧ True")
        session.certify(session.tactic(warm["stateId"], "simp")["nextStateId"])
        root = session.start("∀ m n : Nat, Nat.pow m (n+1) = Nat.pow m n * m")
        middle = session.tactic(root["stateId"], "intro m n")
        for text in ["rw [Nat.pow]", "simp only [Nat.pow]"]:
            rewritten = session.tactic(middle["nextStateId"], text)
            assert rewritten["goals"] and not rewritten["hasUnsafe"], rewritten
        compiler_sequence(session, statement)
        session.finish()


def mathlib_gate(mathlib, env):
    direct = subprocess.run(["lake", "env", "lean", "Test/Mathlib/ScopeControls.lean"],
                            cwd=ROOT, env=env, text=True, capture_output=True, timeout=180)
    assert direct.returncode == 0, direct.stdout + direct.stderr
    entries = []
    with Session(entries, env, ["Mathlib"]) as session:
        session.call("protocol.describe", {})
        for statement in ["∀ (p q : Prop), p ∧ q → q ∧ p", "∀ (p q : Prop), p ∨ q → q ∨ p"]:
            root = session.start(statement)
            middle = session.tactic(root["stateId"], "intro p q")
            assert middle["goals"]
            current = middle["nextStateId"]
            first = middle["goals"][0]["name"]
            inspected = session.call("goal.inspect", dict(stateId=current, goals=[root["root"], first]))
            assert any(value["status"] == "active" for value in inspected["obligations"])
            done = session.tactic(current, "tauto")
            assert not done["goals"] and not done["hasSorry"] and not done["hasUnsafe"]
            session.certify(done["nextStateId"])
            session.call("goal.inspect", dict(stateId=done["nextStateId"], goals=[root["root"], first]))
            session.certify(session.tactic(current, "tauto")["nextStateId"])
        statement = ("∀ (α : Type u_1) (β : Type u_2) (γ : Type u_3) "
                     "[DecidableEq α] (s t u v : Finset α) (a b : α), "
                     "a ∉ s → ((∀ a ∈ t, a ∉ s) ↔ ∀ ⦃a : α⦄, a ∈ s → a ∉ t)")
        root = session.start(statement, ["u_1", "u_2", "u_3"])
        middle = session.tactic(root["stateId"], "intro α β γ inst s t u v a b")
        done = session.tactic(middle["nextStateId"], "tauto")
        assert not done["goals"] and not done["hasSorry"] and not done["hasUnsafe"]
        session.certify(done["nextStateId"])
        # Coupled siblings remain queryable after one selected branch is solved.
        root = session.start("∀ (p q : Prop), (p ∧ q → q ∧ p) ∧ (p ∨ q → q ∨ p)")
        middle = session.tactic(root["stateId"], "intro p q; constructor")
        names = [goal["name"] for goal in middle["goals"]]
        assert len(names) == 2
        first = session.tactic(middle["nextStateId"], "tauto", 1)
        inspected = session.call("goal.inspect", dict(stateId=first["nextStateId"], goals=names))
        assert {value["status"] for value in inspected["obligations"]} == {"active", "complete"}
        last = session.tactic(first["nextStateId"], "tauto")
        session.certify(last["nextStateId"])
        # The reported search context: compiler-producing simp under Mathlib.
        compiler_sequence(session, "∀ m n : Nat, Nat.pow m n = Nat.pow m n")
        root = session.start("∀ m n : Nat, 0 < Nat.pow (m+1) n")
        middle = session.tactic(root["stateId"], "intro m n")
        simp = session.tactic(middle["nextStateId"], "cases n <;> simp [Nat.pow]")
        assert not simp["hasSorry"] and not simp["hasUnsafe"]
        session.finish()
    diagnostic = subprocess.run([str(ROOT / ".lake/build/bin/scope_diagnostic")], cwd=ROOT,
                                env=env, text=True, capture_output=True, timeout=180)
    assert diagnostic.returncode == 0, diagnostic.stderr
    result = json.loads(diagnostic.stdout)
    assert result["validator"] == "accepted" and result["rootCertificate"]["status"] == "certified"
    assert any(not record["rootReachable"] and record["missingInOwner"] for record in result["assignments"])
    assert result["auxiliaryAudit"]
    return entries, result, direct.stdout + direct.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, help="Explicit pinned Mathlib checkout/build for the separate gate")
    parser.add_argument("--mathlib-reference", type=Path, help="Git object database containing the pinned Mathlib commit")
    parser.add_argument("--capture", type=Path)
    args = parser.parse_args()
    mathlib = args.mathlib.resolve() if args.mathlib else None
    source_verification = verify_mathlib_sources(mathlib, args.mathlib_reference or mathlib) if mathlib else None
    env = environment(mathlib)
    core = core_gate(env)
    math, diagnostic, ordinary = mathlib_gate(mathlib, env) if mathlib else ([], None, None)
    if args.capture:
        args.capture.mkdir(parents=True, exist_ok=True)
        data = dict(source_base=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                    source_uncommitted=True, binary_sha256=hashlib.sha256((ROOT / ".lake/build/bin/repl").read_bytes()).hexdigest(),
                    toolchain=(ROOT / "lean-toolchain").read_text().strip(), core=core, mathlib=math,
                    diagnostic=diagnostic, ordinary_lean=ordinary, mathlib_source_verification=source_verification)
        (args.capture / "capture.json").write_text(json.dumps(data, indent=2) + "\n")
    print(f"PASS: {len(core)} core and {len(math)} Mathlib exchanges; validation version {VERSION}, compiler-producing transitions, kernel receipts, lifecycle, and fatal integrity failures")


if __name__ == "__main__":
    main()
