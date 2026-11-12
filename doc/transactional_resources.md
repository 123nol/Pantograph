# Transactional resource errors: protocol revision 3

`protocol.describe` reports `protocolVersion: 3`, `resourceErrorVersion: 2`, and
`commandTransactionVersion: 1`. Model expressions, transition provenance,
inspection, messages, and certification keep their version-1 representations.
Transition validation now uses [version 3](compiler_aware_validation.md). Startup still emits `ready.`.

Every subsequent response is one compact JSON line. Diagnostic newlines are
escaped inside strings. The `printJsonPretty` option has been removed from both
option structures and command handling. Clients must migrate to revision 3;
there is no revision-2 negotiation or human-readable stdout parser.

[The error schema](transactional_resources.schema.json) and
[shared error fixtures](transactional_resources.fixtures.json) define the two
new error envelopes. Error envelopes contain no allocation IDs, success flags,
validation results, or certification receipts. Existing ordinary argument and
tactic errors retain their representations. Human descriptions are bounded;
clients classify errors through fields rather than descriptions.

A resource error includes `resource.version: 2`, a `resource.kind`, a phase
(`execute`, `validate`, `observe`, or `serialize`), and a positive
`resource.limit` in that kind's units:

- `heartbeats`: the limit uses Lean's `maxHeartbeats` option units; each unit
  counts one thousand underlying heartbeats. It does not measure elapsed seconds.
- `recursion-depth`: Lean's `maxRecDepth` was reached (`throwMaxRecDepthAt`,
  recognized with Lean's `Exception.isMaxRecDepth`). The limit is in recursive
  nesting levels: the bound of the innermost `set_option maxRecDepth N in` scope
  (tactic or term) that the exception left, or else the command's configured
  `maxRecDepth`. Each scope records its bound before its context unwinds, so
  nested scopes report the inner one, and a raised bound is reported as raised.
  A `by` block inside a term scope is elaborated after that scope exits, so the
  outer bound is the one that applied to it. Limits changed programmatically by
  tactic code (`withAtLeastMaxRecDepth`, Mathlib's `sudo set_option`) are not
  captured.

Version 2 replaces version 1; there is no version-1 negotiation. A known
resource cause does not by itself make the session reusable: recovery follows
the rules below for both kinds.
Unexpected exceptions produce `error: "internal"` with
`recovery: "session-unusable"`.

## Command ownership and recovery

All dispatch operations use `Repl.runTransaction`, including `goal.continue`,
`env.add`, `frontend.process`, options, deletion, reset, and read-only commands.
The runner copies the complete REPL state and gives the command a separate
Lean Core state reference. The copies include the retained allocation table,
allocation counter, options, environment, message log, caches, name generator,
macro scopes, and information/trace state. Term and meta state live inside the
retained snapshots or temporary command monads.

Only successful response encoding publishes the staged REPL and Core states.
Failure discards the staged references. Recovery requires no execution of
restoration code under an exhausted Lean budget. Existing live IDs retain their
snapshots, and a failed allocation cannot appear in `stat`. IDs may be reused
when their staged allocation was never published; they never collide with a
live allocation. Reset retains its established semantics of clearing all
allocations and restarting IDs.

A classified resource failure returns `recovery: "command-rolled-back"` only
when discarding the staged state establishes recovery. Ordinary failures may
still return their established diagnostics. A validation integrity failure also
discards staged state, emits the existing validation envelope, and ends the session.
An unexpected exception makes the
session unusable. Further native dispatch is refused, and the executable stops
reading commands after writing the fatal response and exits nonzero.

`frontend.process` can execute module initializers and write an output file.
Its resource failures therefore use `session-unusable`, and unexpected frontend
IO failures are fatal. Lean's command elaborator reports a recursion-depth
failure inside a processed file as that command's error message, as when
compiling the file, so such a file returns its messages normally. Successful frontend operations retain their existing
results. Rollback never promises to reverse arbitrary external IO performed
by tactics. This protocol does not sandbox tactics.

Response bytes exist before publication. Output uses one complete line followed
by a flush. A failed or partial write ends the process without attempting a
second response. Startup and transport failures use bounded stderr diagnostics.
Native crashes and OS termination can prevent even a best-effort error response.

## Budgets and phases

Each transaction uses `Lean.withCurrHeartbeats` once. Saved goal contexts restore
state, not the Core reader's heartbeat origin. Phase wrappers check the same
finite budget before and after work; none resets that origin. Pure validation,
transition construction, goal observation, diagnostic rendering, and compact
JSON encoding are included. Pure/IO operations that do not poll Lean are checked
when they return; this is a computation allowance, not preemptive cancellation.

On the pinned Lean 4.10.0-rc1 toolchain, `Exception.isMaxHeartbeat` recognizes the
exception produced by `Core.throwMaxHeartbeat`. The classifier additionally
requires the current counter to exceed the current positive budget. It attaches
the explicit phase and limit before unwinding the relevant context. It does not
format an exception to classify it. Ambiguous failures terminate the session.

Frontend info-tree observation now runs in CoreM under the caller's budget,
instead of using `ContextInfo.runMetaM`, which re-entered IO with a new origin.
Frontend compilation receives the remaining allowance for each source command,
with checks between compilation and observation. Lean's own frontend can still
create internal scopes, so outer checks enforce the total request allowance.
All repository callers were migrated to the shared CoreM frontend interface.

`goal.certify` keeps its positive, explicit kernel allowance and existing outcome
schema. That allowance applies to each direct kernel declaration check, as in
revision 2; it is not a new wall-clock deadline. If the outer command allowance
is exhausted, the transaction discards staged state and returns a literal
`inconclusive` certification result without a receipt. Neither kernel exhaustion
nor outer exhaustion creates a certificate. Minimal error and inconclusive
responses are constructed in IO without Lean pretty printing or type reduction.

The existing native `--maxHeartbeats=<positive integer>` option configures the
command allowance. Zero is rejected at startup. No application JSON budget
setting was added. `--pantograph.traceCommands=true` emits bounded JSON traces
to stderr, including command, truncated tactic, selected state/goal, phase, and
underlying heartbeat usage. Tracing is off by default.

## Verification and delivery

Run `lake build repl test`, `lake test`, and
`lake env python3 scripts/test_transactional_resources.py --capture pantograph_backport/transactional_resources/capture.json`.
The native suite exercises staged mutation failures in every phase, request
accounting, retained state reuse, and fatal refusal. The raw executable harness
uses genuine Lean reduction exhaustion and lazy diagnostic rendering, then
certifies a simple proof in the same session. It also checks failed starts,
cleanup, compact multiline diagnostics, bounded stderr tracing, fatal shutdown,
frontend exhaustion, and a broken stdout pipe.

Discarding an isolated state reference removes the restoration procedure whose
failure would otherwise need fault injection. Tests mutate staged state before
exhaustion and confirm that original state remains available. Unexpected internal
exceptions still exercise the fatal path. Phase injection supplements the real
native heartbeat reproduction; it does not replace it.

See [the deployment handoff](../pantograph_backport/transactional_resources/README.md)
for identities, evidence limits, and remaining companion/deployment gates.
