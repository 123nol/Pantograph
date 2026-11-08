# Elaboration aborts and fatal failure diagnostics

## Elaboration aborts are ordinary failures

Lean's elaborator reports some errors by logging them and then throwing an
internal *abort* exception (`abortTactic`, `abortTerm`, `abortCommand`). `exact`,
`refine` and `have` do this when a placeholder cannot be synthesized:

```text
don't know how to synthesize placeholder for argument 'x'
```

Lean's own tactic runner (`Elab.Tactic.run`) catches these aborts. The REPL runs
tactics through `GoalState.step` instead, and `rethrowInfrastructure` re-raised
every internal exception, so each abort reached the transaction boundary as
`{"error":"internal","desc":"Unexpected REPL command failure","recovery":"session-unusable"}`
and ended the session. Sampled RL proposals hit this constantly: a lemma applied
with arguments Lean cannot infer is one of the most common invalid tactics.

`rethrowInfrastructure` now lets elaboration aborts through to the caller's
ordinary error path, and `failureText` reports the error the abort logged.
`goal.tactic` and the other tactic operations return the normal
`tacticErrors`/`messages` failure, the input state stays usable, and nothing
is allocated. `goal.start`, `expr.echo` and declaration elaboration report the
logged error the same way. Other internal exceptions, resource exhaustion and
runtime limits keep their existing handling. The stdout protocol and its
versions are unchanged: the failure uses the existing tactic-failure response.

## Fatal failure diagnostic, version 1

An unexpected command failure still returns exactly one stdout response,
`{"error":"internal","desc":"Unexpected REPL command failure","recovery":"session-unusable"}`,
and the process still exits. Before that response, the REPL writes one JSON line
to stderr:

```json
{"kind":"pantograph-command-failure","version":1,"repl_command_sequence":3,
 "operation":"goal.tactic","state_id":0,"goal_index":0,"phase":"execute",
 "exception_category":"internal","internal_exception_id":"pantographCommandResource",
 "detail":"internal exception #16","detail_truncated":false,"render_status":"rendered"}
```

| Field | Meaning |
| --- | --- |
| `kind`, `version` | `pantograph-command-failure`, `1` |
| `repl_command_sequence` | Commands this process has dispatched, counting the failed one. Independent of any client counter. |
| `operation`, `state_id`, `goal_index` | The command and its `stateId` (or `target`) and `goalId`, or `null` |
| `phase` | Innermost protected phase the exception left (`execute`, `validate`, `observe`, `serialize`), or `unknown` |
| `exception_category` | `internal`, `runtime` (heartbeat or recursion limit) or `error` |
| `internal_exception_id` | Registered name of an internal exception, otherwise `null` |
| `detail` | The exception's rendered message, cut to at most 2048 UTF-8 bytes, or `null` if rendering failed |
| `detail_truncated`, `render_status` | Whether the detail was cut; `rendered` or `failed` |

The whole line is at most 4096 bytes including JSON escaping; the detail is cut
further if escaping would exceed that. Rendering and writing are isolated: a
rendering failure gives `render_status: "failed"`, and a write failure changes
nothing else. Validation failures and resource rollbacks keep their own
responses and write no record. The record carries no expressions, environment
data or tactic text; the client's request record carries the command.

The phase belongs to the exception that reaches the boundary. Each phase
records the exception leaving it unless an inner phase already recorded that
same exception object, so an exception keeps its innermost phase. An exception
that was caught does not lend its phase to a later, different failure: that
failure gets the phase it actually left, or `unknown` if it left none.

`pantograph.traceCommands` remains a Lean launch option for full command
traces. The failure record needs no option.

## Verification

- `lake test`: `FailureBoundary` covers the four placeholder tactics, state
  reuse and certification after them, and the record's byte bound, escaping,
  truncation flag and failed rendering.
- `lake env python3 scripts/test_failure_diagnostics.py [--mathlib PATH]`:
  native sessions for the aborts (with and without Mathlib), the record for an
  injected internal failure and an unrenderable error, and an ordinary
  rejection without a record. `Test.ContractFixtures` provides the injection
  tactics; they are test-only.
