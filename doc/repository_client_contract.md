# Repository-owned client companion contract

Stage 4 extends merged PR #1 at
`0dd5d2225e2d093f66a4b6231c1aa35004f2c8f3` on `client_centric_repo`.
The Lean toolchain and Mathlib deployment pin remain unchanged.

`protocol.describe {}` identifies `maths-ai-pantograph`, protocol version 2,
model S-expression version 1, transition validation version 1, message version 1,
`explicit-focused-v1` goal selection, and `string-array-v1` tactic errors.
Version 2 adds transition provenance and `goal.inspect`; see
[snapshot_protocol.md](snapshot_protocol.md).
The planning document's contract revision 2 is not a runtime compatibility mode.

Successful `goal.tactic` responses retain `nextStateId`, `goals`, `messages`,
`hasSorry`, and `hasUnsafe`. They also carry
`validation: {version: 1, scope: "transition-expressions", checked: true}`.
The metadata states that the defined expression checks completed. A positive
admission or unsafe flag remains a successful allocation for the client to delete
before rejecting that candidate. Missing or cyclic evidence returns a command
error with category `validation` and allocates no result state.

The shared operation transaction captures diagnostics and restores its caller's
meta, elaborator, environment, message, trace, information, and declaration-cache
state. Fresh-name counters remain monotonic. Logged errors reject execution even
when tactics return normally. Thrown errors retain their diagnostics. Warnings
and information survive success. Tagged messages retain their kind. Source
strings use their real source maps; unavailable positions are exactly `(0, 0)`.
Snapshot serialization and diagnostics also restore their caller.

The parser runs full tactic or conversion sequences with end-of-input checking.
Deferred synthetic elaboration runs inside the transaction. Default synthesis
resolves ordinary implicit arguments. Partial synthesis runs deferred tactics
while permitting unresolved typeclass obligations. Reachable unresolved holes
remain goals. This applies to goal initialization as well as subsequent operations.

Validation inspects the selected goal, input and returned goals, new or changed
ordinary and delayed assignments, new local contexts, and pending synthetic
expressions. It follows ordinary assignments and delayed pending assignments,
local types and values, constant dependencies, and projection dependencies.
Admission scanning uses elaborated terms rather than tactic strings. Unsafe
scanning concerns resulting proof dependencies rather than the implementation
of the tactic elaborator.

Each state retains its original trust environment. Dependency traversal stops at
that environment but still checks directly referenced constants for unsafe status.
New reachable declarations have their types and values scanned recursively,
including declarations retained from earlier transitions. Imported Mathlib
remains the trust basis. This does not audit all imported axioms or kernel-certify
an assembled theorem reconstructed from independent search nodes.

Safety scanning covers changed assignments even when they are no longer visible.
Obligation retention follows the selected, input and returned goals and their
reachable expressions. Discarded elaboration variables are not all promoted to
user goals. Existing dormant siblings retain manual-mode behavior. A retained
conversion equation owns its evolving right-hand placeholders until conversion
exit; unresolved holes after exit remain obligations. Cyclic expression
assignments and missing declarations fail validation.

All existing structured operations use the shared transaction: assignment,
have/let/define, calc, motivated application, no-confusion, and conversion
entry/exit. The merged omitted-index default, nonzero selection, sibling resumption,
mode metadata and automatic final-conversion exit remain supported. Repeated
references to the same resumed goal are removed while preserving order.

The model serializer's expression normalization, fields, binder roles and local
indices are unchanged. Its snapshot reads now restore their caller. Complete
sequence parsing and synthetic elaboration can change fresh internal names;
normalized expressions, graph fingerprints, node features and edges retain their
canonical meaning.

Verification: `lake build repl Test.ContractFixtures` and `lake test` pass.
The suite contains 299 assertions, including 37 Stage 4 assertions. Existing
Python codec, reconciliation, environment and model tests report 316 passes.
The final diagnostic records 61 raw Mathlib exchanges against the existing codec,
four unchanged canonical graph goldens, zero final allocations, and confirmed
subprocess reaping. The sandboxed diagnostic's shutdown timeout is not counted
as a pass; the recorded final capture ran outside that sandbox.

The tracked patch, source hashes, executable hash and live evidence are in
`pantograph_backport/`. The build reused a copied archive dependency/build cache
and rebuilt changed targets. Stage 7's fresh release reproduction remains pending.
Stage 5 actual-client integration, Stage 6 production migration, and Stage 8
RL/deployment validation remain pending. No fork publication, dependency migration
or RL launch is part of Stage 4.
