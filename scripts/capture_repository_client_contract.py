#!/usr/bin/env python3
"""Capture Stage 4 wire evidence and check it against the existing application codec.

Run with the application's Python environment. Output must be a new directory.
Historical captures are read as replay inputs and are never modified.
"""
from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

BASE = "0dd5d2225e2d093f66a4b6231c1aa35004f2c8f3"


async def capture(args):
    repo = args.repo.resolve()
    application = args.application.resolve()
    fixtures = application / "maths_ai/gnn_inference/tests/fixtures/pantograph"
    sys.path.insert(0, str(application))
    from maths_ai.hybrid_reasoner.pantograph_protocol import (
        decode_json_response, decode_response, decode_execution_goal,
    )
    from maths_ai.gnn_inference.atp_lean_gnn.graph import dag_fingerprint, model_goal_to_dag

    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip() == BASE
    toolchain = (repo / "lean-toolchain").read_text().strip()
    assert toolchain == (args.mathlib / "lean-toolchain").read_text().strip()
    env = os.environ.copy()
    mathlib_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=args.mathlib, text=True,
    ).strip()
    own_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, text=True,
    ).strip()
    # Lake may return relative package paths; resolve them against each owning project.
    def absolute_paths(value, owner):
        return os.pathsep.join(str((owner / p).resolve()) if not Path(p).is_absolute() else p
                               for p in value.split(os.pathsep) if p)
    env["LEAN_PATH"] = absolute_paths(own_path, repo) + os.pathsep + absolute_paths(mathlib_path, args.mathlib)
    repl = repo / ".lake/build/bin/repl"
    proc = await asyncio.create_subprocess_exec(
        "stdbuf", "-oL", str(repl), "Mathlib", "Test.ContractFixtures",
        cwd=repo, env=env, stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
    )
    stderr_task = asyncio.create_task(proc.stderr.read())
    entries = []
    allocated = set()
    graph_checks = []
    try:
        ready = (await asyncio.wait_for(proc.stdout.readline(), 30)).decode().rstrip("\n")
        assert ready == "ready.", ready

        async def call(label, command, payload, *, owned=True):
            line = command + " " + json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
            proc.stdin.write((line + "\n").encode())
            await proc.stdin.drain()
            response_line = (await asyncio.wait_for(proc.stdout.readline(), 30)).decode().rstrip("\n")
            response = decode_json_response(response_line)
            if owned:
                decode_response(command, response)
            entries.append(dict(label=label, command=command, request=payload,
                                request_line=line, response_line=response_line, response=response))
            for key in ("stateId", "nextStateId"):
                if key in response:
                    allocated.add(response[key])
            if command == "goal.delete":
                allocated.difference_update(payload["stateIds"])
            return response

        upstream = json.loads((fixtures / "upstream_pr1/capture.json").read_text())
        golden = json.loads((fixtures / "canonical_graph_expectations.json").read_text())["goals"]
        id_map = {}
        renames = {
            "unsupported_descriptor": "descriptor",
            "admission_flag_present_without_validation": "checked_admission",
            "logged_error_still_succeeds_without_diagnostics": "logged_error_rejected",
        }
        for old in upstream["interactions"]:
            payload = dict(old["request"])
            if "stateId" in payload:
                payload["stateId"] = id_map.get(payload["stateId"], payload["stateId"])
            if "stateIds" in payload:
                payload["stateIds"] = sorted(allocated)
            label = renames.get(old["label"], old["label"])
            result = await call(label, old["command"], payload)
            for key in ("stateId", "nextStateId"):
                if key in old["response"] and key in result:
                    id_map[old["response"][key]] = result[key]
            if label in golden:
                actual = result["goals"]
                expected = golden[label]
                assert len(actual) == len(expected)
                for wire, target in zip(actual, expected):
                    goal = decode_execution_goal(wire).goal
                    canonical = goal.model_dump()
                    assert canonical == target["canonical"], (label, canonical, target["canonical"])
                    assert goal.state_fingerprint() == target["state_fingerprint"]
                    dag = model_goal_to_dag(goal)
                    assert dag_fingerprint(dag) == target["dag_fingerprint"]
                    assert [node.as_dict() for node in dag.nodes] == target["nodes"]
                    assert [list(edge) for edge in dag.edges] == target["edges"]
                    assert dag.expression_root_id == target["expression_root_id"]
                    assert dag.state_root_id == target["state_root_id"]
                graph_checks.append(label)
            if label == "logged_error_rejected":
                assert result.get("tacticErrors") == ["capture error"]
                assert "nextStateId" not in result
                assert result["messages"][0]["data"] == "capture error"

        root = (await call("validation_start", "goal.start", {"expr": "True"}))["stateId"]
        for label, text, flag in [
            ("skip", "skip", None),
            ("warning_info", 'run_tac Lean.logWarning "warning evidence"\nrun_tac Lean.logInfo "information evidence"\ntrivial', None),
            ("tagged_warning", "contract_tagged_warning", None),
            ("nested_admission", "exact (by sorry)", "hasSorry"),
            ("local_admission", "have h : True := by sorry\nexact h", "hasSorry"),
            ("introduced_dependency_admission", "contract_dependency_sorry", "hasSorry"),
            ("positive_unsafe", "contract_unsafe", "hasUnsafe"),
            ("hidden_hole", "contract_hidden_hole", None),
            ("delayed_hole", "contract_delayed_hole", None),
            ("hidden_local_value", "contract_hidden_local_value", None),
            ("missing_assignment", "contract_missing_assignment", "validation"),
            ("failed_snapshot_mutation", "contract_failed_mutation", "failure"),
            ("reuse_after_failure", "trivial", None),
            ("trailing_input", "trivial\nthis_is_not_a_tactic", "parse"),
        ]:
            result = await call(label, "goal.tactic", {"stateId": root, "goalId": 0, "tactic": text})
            if flag in ("hasSorry", "hasUnsafe"):
                assert result[flag] is True and result["validation"]["checked"] is True
            elif flag == "failure":
                assert "tacticErrors" in result and "nextStateId" not in result
            elif flag == "validation":
                assert result.get("error") == "validation" and "nextStateId" not in result
            elif flag == "parse":
                assert "parseError" in result and "nextStateId" not in result
            else:
                assert "nextStateId" in result
            if label in ("hidden_hole", "delayed_hole", "hidden_local_value"):
                assert len(result["goals"]) == 1
                solved = await call(label + "_solved", "goal.tactic", {
                    "stateId": result["nextStateId"], "goalId": 0, "tactic": "trivial",
                })
                assert solved["goals"] == []
            if label == "skip":
                assert len(result["goals"]) == 1
            if label == "warning_info":
                assert {m["severity"] for m in result["messages"]} == {"warning", "information"}
            if label == "reuse_after_failure":
                assert result["messages"] == []
        stored = await call("store_admission", "goal.tactic", {
            "stateId": root, "goalId": 0, "tactic": "contract_store_admission",
        })
        used = await call("use_stored_admission", "goal.tactic", {
            "stateId": stored["nextStateId"], "goalId": 0, "tactic": "exact ContractFixtures.storedAdmission",
        })
        assert used["hasSorry"] is True
        identity = (await call("multiline_start", "goal.start", {"expr": "∀ (p : Prop), p → p"}))["stateId"]
        result = await call("multiline_complete", "goal.tactic", {
            "stateId": identity, "goalId": 0, "tactic": "intro p h\nexact h",
        })
        assert result["goals"] == []
        # Exercise extra merged server operations without pretending they are owned-client APIs.
        conv = (await call("conversion_start", "goal.start", {"expr": "(1 + 2) + 3 = 6"}))["stateId"]
        result = await call("conversion_enter", "goal.tactic", {"stateId": conv, "mode": "conv"}, owned=False)
        for index, text in enumerate(["lhs", "congr", "rfl", "rfl"]):
            result = await call(f"conversion_step_{index}", "goal.tactic", {
                "stateId": result["nextStateId"], "goalId": 0, "tactic": text,
            }, owned=False)
        assert [g["fragment"] for g in result["goals"]] == ["tactic"]
        await call("validation_delete_all", "goal.delete", {"stateIds": sorted(allocated)})
        assert (await call("validation_final_stat", "stat", {}))["nGoals"] == 0
        proc.stdin.close()
        await asyncio.wait_for(proc.wait(), 10)
        stderr = (await stderr_task).decode()
        assert proc.returncode == 0, stderr
        args.output.mkdir(parents=True, exist_ok=False)
        artifact = dict(kind="stage4-companion-live-capture", readiness_line=ready,
                        interactions=entries, graph_checks=graph_checks,
                        exit_code=proc.returncode, stderr=stderr,
                        subprocess_reaped=True, final_allocations=len(allocated))
        (args.output / "capture.json").write_text(json.dumps(artifact, ensure_ascii=False, indent=2) + "\n")
        provenance = dict(base_commit=BASE, toolchain=toolchain,
                          lean_version=subprocess.check_output(["lake", "env", "lean", "--version"], cwd=repo, text=True).strip(),
                          repl_path=str(repl), repl_sha256=hashlib.sha256(repl.read_bytes()).hexdigest(),
                          imports=["Mathlib", "Test.ContractFixtures"], lean_path=env["LEAN_PATH"],
                          mathlib_expected_pin="29dcec074de168ac2bf835a77ef68bbe069194c5",
                          mathlib_pin_verification="archive has no Git metadata; expected deployment pin",
                          build_cache="copied reference archive cache; changed targets rebuilt",
                          python_executable=sys.executable,
                          decoder="existing revision-2 application codec", exchanges=len(entries),
                          graph_checks=graph_checks, initial_state_count=0, final_state_count=0,
                          subprocess_reaped=True, complete_theorem_certification=False)
        (args.output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
        print(json.dumps(dict(exchanges=len(entries), graph_checks=graph_checks, output=str(args.output))))
    finally:
        if proc.returncode is None:
            proc.kill()
            await proc.wait()
        if not stderr_task.done():
            await stderr_task


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--application", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    asyncio.run(capture(parser.parse_args()))


if __name__ == "__main__":
    main()
