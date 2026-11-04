#!/usr/bin/env python3
"""Raw executable regression and revision-3 capture; no application client required."""
import argparse
import hashlib
import json
from pathlib import Path
import selectors
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


class Session:
    def __init__(self, entries, *options):
        self.entries = entries
        self.stderr = tempfile.TemporaryFile(mode="w+t")
        self.proc = subprocess.Popen(
            ["lake", "env", str(ROOT / ".lake/build/bin/repl"), "Init",
             "Test.ContractFixtures", *options], cwd=ROOT, text=True,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr)
        self.read = selectors.DefaultSelector()
        self.read.register(self.proc.stdout, selectors.EVENT_READ)
        assert self.line() == "ready."

    def line(self):
        assert self.read.select(20), "REPL response timed out"
        return self.proc.stdout.readline().rstrip("\n")

    def call(self, command, payload, record=True):
        request = command + " " + json.dumps(payload, separators=(",", ":"))
        self.proc.stdin.write(request + "\n")
        self.proc.stdin.flush()
        line = self.line()
        response = json.loads(line)
        assert "Uncaught IO exception" not in line
        if record:
            self.entries.append(dict(command=command, request=payload,
                                     request_line=request, response_line=line, response=response))
        return response

    def close(self, fatal=False):
        self.proc.stdin.close()
        status = self.proc.wait(timeout=20)
        assert (status != 0) if fatal else (status == 0), status
        assert self.proc.stdout.read() == "", "unsolicited or duplicate stdout"
        self.stderr.seek(0)
        stderr = self.stderr.read()
        self.stderr.close()
        self.read.close()
        return stderr


def run():
    entries = []
    session = Session(entries, "--maxHeartbeats=100", "--pantograph.traceCommands=true")
    descriptor = session.call("protocol.describe", {})
    assert descriptor["protocolVersion"] == 3
    assert descriptor["resourceErrorVersion"] == descriptor["commandTransactionVersion"] == 1
    root = session.call("goal.start", {"expr": "True"})
    for _ in range(3000):
        assert session.call("stat", {}, record=False) == {"nGoals": 1}
    for tactic, phase in [("contract_heartbeat", "execute"),
                          ("contract_diagnostic_heartbeat", "observe")]:
        error = session.call("goal.tactic", {"stateId": root["stateId"], "tactic": tactic})
        assert error == dict(error="resource", desc="Lean command heartbeat budget exhausted",
                             recovery="command-rolled-back", resource=dict(
                                 version=1, kind="heartbeats", phase=phase, limit=100))
        assert session.call("stat", {}) == {"nGoals": 1}
    failed = session.call("goal.start", {"expr": "by contract_heartbeat"})
    assert failed["error"] == "resource" and failed["recovery"] == "command-rolled-back"
    assert session.call("stat", {}) == {"nGoals": 1}
    ordinary = session.call("goal.tactic", {"stateId": root["stateId"],
                                            "tactic": 'fail "first line\\nsecond line"'})
    assert "tacticErrors" in ordinary and any("\n" in text for text in ordinary["tacticErrors"])
    continued = session.call("goal.continue", {"target": root["stateId"], "goals": [root["root"]]})
    done = session.call("goal.tactic", {"stateId": root["stateId"], "tactic": "exact True.intro"})
    certificate = session.call("goal.certify", {"stateId": done["nextStateId"]})
    assert certificate["status"] == "certified"
    session.call("goal.delete", {"stateIds": [root["stateId"], continued["nextStateId"], done["nextStateId"]]})
    assert session.call("stat", {}) == {"nGoals": 0}
    traces = [json.loads(line) for line in session.close().splitlines()]
    assert any(trace["phase"] == "observe" for trace in traces)
    assert all(len(trace["tactic"]) <= 512 and trace["heartbeats"] > 0 for trace in traces)

    fatal = Session(entries, "--maxHeartbeats=100")
    root = fatal.call("goal.start", {"expr": "True"})
    # Queue a second command before the fatal response. It must never execute.
    fatal.proc.stdin.write('goal.tactic {"stateId":0,"tactic":"contract_internal_failure"}\nstat {}\n')
    fatal.proc.stdin.flush()
    line = fatal.line()
    response = json.loads(line)
    assert response == dict(error="internal", desc="Unexpected REPL command failure",
                            recovery="session-unusable")
    entries.append(dict(command="goal.tactic", request=dict(stateId=0, tactic="contract_internal_failure"),
                        response_line=line, response=response))
    assert "session is unusable" in fatal.close(fatal=True)

    kernel = Session(entries, "--maxHeartbeats=50000", "--maxRecDepth=10000")
    # Distinct leaves prevent shared subexpressions from making the kernel check trivial.
    nodes = [(f"({index} = ({index} : Nat))", f"(Eq.refl {index})") for index in range(512)]
    while len(nodes) > 1:
        nodes = [(f"({left} ∧ {right})", f"(And.intro {lp} {rp})")
                 for (left, lp), (right, rp) in zip(nodes[::2], nodes[1::2])]
    root = kernel.call("goal.start", {"expr": nodes[0][0]})
    done = kernel.call("goal.tactic", {"stateId": root["stateId"], "expr": nodes[0][1]})
    exhausted = kernel.call("goal.certify", {"stateId": done["nextStateId"], "maxHeartbeats": 1})
    assert exhausted["status"] == "inconclusive" and "receipt" not in exhausted
    assert kernel.call("stat", {}) == {"nGoals": 2}
    assert kernel.call("goal.certify", {"stateId": done["nextStateId"]})["status"] == "certified"
    kernel.close()

    frontend = Session(entries, "--maxHeartbeats=100")
    response = frontend.call("frontend.process", {"file": "example : True := by contract_heartbeat", "invocations": False, "sorrys": False})
    assert response["error"] == "resource" and response["recovery"] == "session-unusable", response
    frontend.close(fatal=True)

    broken = Session([], "--maxHeartbeats=100")
    broken.proc.stdout.close()
    broken.proc.stdin.write("stat {}\n")
    broken.proc.stdin.flush()
    broken.proc.stdin.close()
    assert broken.proc.wait(timeout=20) != 0
    broken.read.close()
    broken.stderr.close()

    startup = subprocess.run(["lake", "env", str(ROOT / ".lake/build/bin/repl"), "--maxHeartbeats=0"],
                             cwd=ROOT, text=True, capture_output=True, timeout=20)
    assert startup.returncode != 0 and startup.stdout == "" and startup.stderr
    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", type=Path)
    args = parser.parse_args()
    entries = run()
    if args.capture:
        binary = ROOT / ".lake/build/bin/repl"
        result = dict(protocol_version=3, source_base=subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            source_dirty=bool(subprocess.check_output(["git", "diff", "--name-only"], cwd=ROOT)),
            binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
            toolchain=(ROOT / "lean-toolchain").read_text().strip(),
            imports=["Init", "Test.ContractFixtures"], mathlib=None, exchanges=entries)
        args.capture.parent.mkdir(parents=True, exist_ok=True)
        args.capture.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: native recovery, certification, framing, fatal shutdown, tracing, and broken output ({len(entries)} captured exchanges)")


if __name__ == "__main__":
    main()
