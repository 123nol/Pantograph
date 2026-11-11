#!/usr/bin/env python3
"""Native controls for elaboration aborts and the fatal stderr failure diagnostic.

Run with `lake env python3 scripts/test_failure_diagnostics.py [--mathlib PATH] [--capture DIR]`.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REPL = ROOT / ".lake/build/bin/repl"
PLACEHOLDERS = [
    "exact (fun (x : Nat) => True.intro) _",
    "refine (fun (x : Nat) => True.intro) _",
    "have h := (fun (x : Nat) => x) _",
    "exact (_ : True)",
]
FIELDS = {
    "kind", "version", "repl_command_sequence", "operation", "state_id", "goal_index", "phase",
    "exception_category", "internal_exception_id", "detail", "detail_truncated", "render_status",
}


def session(lines, imports, env):
    """Send all lines at once; return stdout lines, stderr text and exit code."""
    proc = subprocess.run([str(REPL), *imports], cwd=ROOT, env=env, text=True,
                          input="".join(line + "\n" for line in lines), capture_output=True, timeout=600)
    out = proc.stdout.splitlines()
    assert out[0] == "ready.", out[:2]
    return [json.loads(line) for line in out[1:]], proc.stderr, proc.returncode


def records(stderr):
    found = []
    for line in stderr.splitlines():
        try:
            value = json.loads(line)
        except ValueError:
            continue
        if isinstance(value, dict) and value.get("kind") == "pantograph-command-failure":
            found.append(value)
    return found


def abort_control(imports, env, statement="True", closing="trivial"):
    lines = ['goal.start ' + json.dumps({"expr": statement})]
    lines += ['goal.tactic ' + json.dumps({"stateId": 0, "goalId": 0, "tactic": t}) for t in PLACEHOLDERS]
    lines += ['goal.tactic ' + json.dumps({"stateId": 0, "goalId": 0, "tactic": closing}),
              'goal.certify {"stateId":1}', 'goal.delete {"stateIds":[0,1]}', 'stat {}']
    responses, stderr, code = session(lines, imports, env)
    for tactic, response in zip(PLACEHOLDERS, responses[1:]):
        assert "don't know how to synthesize placeholder" in " ".join(response.get("tacticErrors", [])), (tactic, response)
    done, certificate = responses[len(PLACEHOLDERS) + 1], responses[len(PLACEHOLDERS) + 2]
    assert done["nextStateId"] == 1 and done["goals"] == [], done
    assert certificate["status"] == "certified", certificate
    assert responses[-1] == {"nGoals": 0} and code == 0 and not records(stderr)
    return dict(imports=imports, lines=lines, responses=responses)


def fatal_control(tactic, phase, category, env):
    lines = ['protocol.describe {}', 'goal.start {"expr":"True"}',
             'goal.tactic ' + json.dumps({"stateId": 0, "goalId": 0, "tactic": tactic}), 'stat {}']
    responses, stderr, code = session(lines, ["Init", "Test.ContractFixtures"], env)
    assert len(responses) == 3, "a response followed the fatal failure"
    assert responses[2] == {"error": "internal", "desc": "Unexpected REPL command failure",
                            "recovery": "session-unusable"}, responses[2]
    assert code != 0
    found = records(stderr)
    assert len(found) == 1, stderr
    record = found[0]
    assert set(record) == FIELDS and len(json.dumps(record).encode()) <= 4096, record
    assert record["version"] == 1 and record["repl_command_sequence"] == 3
    assert (record["operation"], record["state_id"], record["goal_index"]) == ("goal.tactic", 0, 0)
    assert (record["phase"], record["exception_category"]) == (phase, category), record
    return dict(tactic=tactic, responses=responses, stderr=stderr, record=record)


def ordinary_control(env):
    lines = ['goal.start {"expr":"True"}', 'goal.tactic {"stateId":0,"goalId":0,"tactic":"exact Nat.zero"}',
             'goal.tactic {"stateId":0,"goalId":0,"tactic":"trivial"}']
    responses, stderr, code = session(lines, ["Init"], env)
    assert "tacticErrors" in responses[1] and responses[2]["goals"] == []
    assert code == 0 and not records(stderr)
    return dict(responses=responses)


def environment(mathlib):
    paths = [ROOT / ".lake/build/lib", ROOT / ".lake/packages/LSpec/.lake/build/lib"]
    if mathlib:
        paths += [mathlib / ".lake/build/lib"]
        paths += [p / ".lake/build/lib" for p in (mathlib / ".lake/packages").iterdir() if p.is_dir()]
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths)) + os.pathsep + env.get("LEAN_PATH", "")
    return env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--capture", type=Path)
    args = parser.parse_args()
    env = environment(args.mathlib.resolve() if args.mathlib else None)
    result = dict(
        aborts=[abort_control(["Init"], env)],
        fatal=[fatal_control("contract_internal_failure", "execute", "internal", env),
               fatal_control("contract_unrenderable_error", "observe", "error", env),
               # The same exception keeps its innermost phase.
               fatal_control("contract_inner_phase_failure", "observe", "internal", env),
               # A handled inner failure does not lend its phase to a later one.
               fatal_control("contract_handled_then_internal", "execute", "internal", env)],
        ordinary=ordinary_control(env),
    )
    if args.mathlib:
        result["aborts"].append(abort_control(["Mathlib"], env))
    if args.capture:
        args.capture.mkdir(parents=True, exist_ok=True)
        result.update(
            source_commit=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            binary_sha256=hashlib.sha256(REPL.read_bytes()).hexdigest(),
            toolchain=(ROOT / "lean-toolchain").read_text().strip())
        (args.capture / "capture.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(f"PASS: {len(result['aborts'])} abort sessions, {len(result['fatal'])} fatal diagnostics, ordinary rejection unchanged")


if __name__ == "__main__":
    main()
