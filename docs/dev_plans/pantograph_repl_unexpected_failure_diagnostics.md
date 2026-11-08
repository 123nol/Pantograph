# Custom REPL: unexpected-failure diagnostics and targeted Lean repairs

## Status, repository, and scope

Proposed architecture; obtain explicit verification before implementation.
Target repository: `123nol/Pantograph`, in the maintained custom REPL branch.
Reference source reviewed: `fc740c26a1e832ecb571859af24a5c632a351bd9`.
Verify the actual target branch and base commit before editing; do not modify
an installed executable or the Mathlib checkout directly.

This is the REPL portion of
[puct_pantograph_failure_diagnostics_and_remediation.md](puct_pantograph_failure_diagnostics_and_remediation.md).
It is independently usable by an agent working in the REPL repository.
Related work is described in the
[client plan](pantograph_client_failure_snapshots_and_request_events.md) and
[application plan](mcts_pantograph_failure_bundles_and_replay.md).

The historical PUCT/no-PLN log contains 74 remote internal errors and one hard
timeout across 300 attempts. The original exception and failing request are
absent. Six recoverable observe-phase resource errors and ordinary invalid
tactics are separate outcomes. The run reached all 50 rounds.

The known REPL defect is loss of original unexpected-exception evidence in
`Repl.runTransaction()`. The underlying causes of the 74 errors remain
unconfirmed. Implement safe evidence first, then repair only reproduced Lean
failures. This plan does not promise that diagnostics alone eliminate them.

## Alternatives and decision

| Approach | Advantages | Limits / decision |
|---|---|---|
| Raise heartbeat/time limits | May allow expensive operations to finish | Does not explain or repair unexpected exceptions; not selected globally. |
| Return unexpected exceptions as rejected tactics | Fewer session replacements | Reuses untrusted state and changes semantics; rejected. |
| Add arbitrary fields to stdout error objects | Convenient structured access | Breaks strict downstream decoding unless coordinated; unnecessary for this stage. |
| Enable verbose command tracing for every command | More history | More output; the pinned client cannot enable the core trace option through session options. Not required. |
| Bounded fatal stderr evidence at the shared transaction boundary | Preserves stdout and recovery contracts; captures actual Lean evidence | Requires robust diagnostic rendering and native tests; selected. |

## Architecture and invariants

Primary implementation points:

- `Repl.lean`: shared `runTransaction()` boundary and result encoding.
- `Main.lean`: command write, fatal exit, and transport cleanup.
- `Pantograph/Resources.lean`: phase marking and known resource handling.
- New or existing native transaction/validation regression modules.

Every dispatch path must use the same boundary. Audit execute, validate,
observe, and serialize phases. Do not attach diagnostics only to `goal.tactic`.

Keep the current stdout response schema. An unexpected command exception
still returns exactly one structured `internal` error with recovery
`session-unusable`, followed by normal fatal-session exit. Validation and
resource failures keep their existing separate classifications. Prior state
must never be committed after an unsuccessful transaction.

### Stderr diagnostic contract, version 1

Emit one bounded JSON-line diagnostic for an unexpected fatal command failure.
The line must be independently recognizable among other stderr output:

| Field | Meaning |
|---|---|
| `kind` | Literal `pantograph-command-failure` |
| `version` | Diagnostic schema version, initially 1 |
| `repl_command_sequence` | Monotonically increasing number assigned at the REPL dispatch boundary within one process |
| `operation` | Actual protocol operation that failed |
| `state_id`, `goal_index` | Selected wire state and goal index, when present; otherwise null |
| `phase` | Actual recorded failure phase or `unknown` |
| `exception_category` | Lean exception category before generic error conversion |
| `internal_exception_id` | Internal exception identifier when available, otherwise null |
| `detail` | Bounded original exception description, when safely available |
| `detail_truncated` | Whether the original detail exceeded its byte limit |
| `render_status` | `rendered`, `unavailable`, or `failed` |

These are diagnostic fields on stderr, not new stdout protocol fields.
Client request numbers and `repl_command_sequence` have separate ownership;
do not require numerical equality. The client can correlate the actual pending
serialized request with the fatal diagnostic and retain both numbers.

Store only allowlisted exception-map metadata. Avoid dumping complete
expressions, environments, arbitrary maps, or full tactic text into this
fatal line; the client/application request event carries the command itself.
Set and document a fixed total byte limit, including escaping and metadata.
Truncate detail first, then use a minimal category/ID record if necessary.

### Failure-safe rendering

Capture raw category/ID and phase before unwinding destroys the relevant
context. Human-readable exception rendering may require Lean computation and
can itself exhaust resources or encounter dangling local context.

Attempt rendering with a fresh, strictly bounded diagnostic budget and an
appropriate saved context. This budget must not permit the failed command to
resume or change its transactional state. If rendering fails, emit the raw
category/ID record with `render_status: failed`.

Diagnostic write failure must not replace the original exception, change
recovery, or cause a second stdout response. Avoid recursive logging. Preserve
fatal response delivery and exit even if stderr is unavailable. Record an
unknown phase honestly rather than using a stale success-phase value.

The existing `pantograph.traceCommands` setting is a Lean core launch option.
It is not an accepted `PantographEnv.options` session-print option. Always
emitting the bounded fatal record avoids needing that setting. General trace
configuration is outside this fix.

### Conditional Lean repairs

Do not infer the cause from the last logged tactic or an executable directory
name. Four accepted and four ordinarily rejected small native probes did not
reproduce an internal error.

After the application supplies an exact request/state-history reproducer,
select the repair from its actual failure:

- Incorrect promotion of an ordinary tactic exception: fix the specific
  catch only after proving rollback and subsequent state usability.
- Local/auxiliary metavariable export failure: traverse expressions under the
  correct declaration ownership and context.
- Compiler-generated declaration audit failure: use Lean's real compiler
  provenance and preserve strict kernel-dependency checks.
- Escaped supported resource exhaustion: classify it using structured native
  evidence and the actual rollback outcome.
- Expensive observation/serialization: optimize or bound the measured
  traversal without dropping required model or certification fields.

Preserve missing-local, dangling-reference, unsafe, sorry, unresolved-goal,
and final kernel-certification checks. Never bypass declarations based on
name substrings or classify failures from English error-text matching.

## Sequential implementation stages

### Stage 0 — Establish the native baseline

1. Record the base commit, toolchain, Mathlib pin, current descriptor, and
   transaction tests. Preserve the old built executable separately.
2. Identify a native mechanism for controlled exception injection without
   exposing a production tactic or protocol operation that bypasses checks.
3. Confirm existing classifications for rejection, resource rollback,
   validation failure, unexpected internal failure, and transport failure.

Exit: baseline outcomes and exact test environment are recorded.

### Stage 1 — Implement bounded transaction-boundary diagnostics

Add the version-1 stderr record, process-local command sequencing, actual
phase capture, raw exception evidence, bounded rendering, and write-failure
isolation. Migrate every dispatch/catch path through the shared implementation.

Exit: injected unexpected failures expose useful evidence while stdout,
rollback, and session-fatality behavior remain unchanged.

### Stage 2 — Test and publish the diagnostic handoff

Exercise failures in each phase, rendering failures, very large details,
Unicode/JSON escaping, stderr write failures, and normal commands. Build a
real executable and record its SHA-256 and full source commit.

Deliver to client/application agents:

- The field table, byte limits, and sample native stderr records.
- Existing stdout internal/resource/validation samples proving unchanged
  schemas and recovery values.
- Build/toolchain/Mathlib identities and native test commands/results.
- Explicit statement that the original 74 causes are still unconfirmed.

Exit: client tests can consume real bounded diagnostic fixtures without a
stdout protocol migration.

### Stage 3 — Repair reproduced Lean defects

Take minimized model-free fixtures from the application. Preserve exact
error signature and environment while reproducing. Apply one justified shared
repair per distinct cause and audit adjacent traversal/catch paths for the
same defect. Keep unrelated policy and performance changes out of this work.

Exit: each claimed fix has a deterministic before/after regression, ordinary
rejection or successful transition as appropriate, and final kernel checking
when a complete proof is expected.

### Stage 4 — Rebuild and deployment handoff

Publish the final full commit and executable hash after native regression
checks. Keep the previous executable until application environment rebinding
has completed. A stderr-only diagnostic change does not require a stdout
protocol-version increase. Any later wire change requires a separately
reviewed descriptor/decoder migration.

## Required tests

- One stdout response and one bounded fatal diagnostic per injected unexpected
  command failure; no extra response on rendering/write failure.
- Correct operation/state/goal/phase for execute, validate, observe, serialize,
  inspection, certification, and deletion failures.
- Safe raw diagnostic after an exhausted budget, failed pretty-printer, or
  exception whose original context is unavailable.
- Strict output byte bounds, valid JSON escaping, explicit truncation, and
  independent process-local sequencing.
- Ordinary tactic rejection keeps the input state usable; safe resource
  rollback preserves prior states; internal/validation integrity failures
  invalidate the session.
- No committed allocation or environment mutation after failed transaction
  encoding. Preserve one-response behavior and fatal exit.
- Repaired real cases preserve unsafe/sorry/missing-dependency negative
  controls and final kernel certification.

## Acceptance and limits

The diagnostic phase is complete when native unexpected command failures
retain bounded original evidence without changing recovery or protocol stdout.
The root-cause phase is complete only for the reproduced signatures actually
repaired. An unreproduced historical error must remain documented as unknown.
No client package or application changes belong in this repository's patch.
