# Repository-owned REPL contract

`protocol.describe {}` identifies `maths-ai-pantograph`, protocol version 3,
transition validation version 3, and the existing version-1 model expressions,
transition provenance, inspection, certification, messages, resource errors, and
command transactions. Goal selection is `explicit-focused-v1`; tactic errors use
`string-array-v1`.

Successful `goal.tactic` responses retain `nextStateId`, `goals`, `messages`,
`hasSorry`, and `hasUnsafe`. Validation metadata is exactly
`{version: 3, scope: "execution-closure-and-representation-aware-audit", checked: true}`.
See [the scope-aware contract](scope_aware_validation.md),
[the representation-aware audit](compiler_aware_validation.md) and
[the ownership inventory](scope_aware_ownership.md).

A positive admission or unsafe flag remains a successful allocation for the
client to release before rejecting that candidate. Certification refuses retained
admissions and unsafe dependencies, including unused local values that binding
abstraction would otherwise erase. Kernel checking remains mandatory.

A genuine validation integrity failure returns `error: "validation"`, allocates
no result, discards staged state, and ends the session. It is not an ordinary
tactic rejection or a resource outcome. Ordinary argument and tactic errors retain
their existing payloads. Unknown caller-supplied obligation names remain argument
or index errors; known records must pass strict validation before inspection or
resumption. There is no permissive validation-version fallback.

[Transactional resource errors](transactional_resources.md) defines command
budgets, rollback, bounded reporting, compact stdout lines, and fatal transport
behavior. Snapshot operations restore their caller's meta, elaborator,
environment, message, trace, information, and declaration-cache state. Failed
staged IDs are never published; live allocation IDs remain distinct.

The parser accepts full tactic/conversion sequences with end-of-input checking.
Default and partial synthetic elaboration remain inside the command transaction.
Warnings and information survive successful execution; logged errors reject the
candidate. Tagged messages retain their kinds. Source strings use their actual
source maps; unavailable positions are `(0, 0)`.

Execution closure roots cover the original statement, active and historical
published obligations, siblings, conversion/calculation metadata, pending and
synthetic elaboration, let-rec work, and postponed constraints. Local declarations
are checked in their own context prefixes. Delayed assignments use their pending
owner's abstraction variables. The auxiliary audit preserves detectable admission
and unsafe evidence without promoting inert scratch holes to proof goals.

All REPL allocation paths validate snapshots before publication, including starts,
tactics, continuations, and frontend-generated obligations. Native operation
exports also invoke the shared transition validator. Lower-level goal-building
helpers remain available for internal construction and native diagnostic tests;
their raw intermediate results are not a publication boundary.

The original trust environment remains fixed for a lineage. New retained
constants have closed declaration owners and are scanned recursively. Imported
Mathlib is the transition trust basis. Final certification separately scans the
proof's transitive dependencies and invokes the kernel on the complete original
root statement.

Transition provenance, explicit/nonzero goal selection, manual sibling dormancy,
conversion exit, model normalization, local identities, and serialization fields
retain their existing representations. See [retained snapshots](snapshot_protocol.md).

Current native evidence and separate Mathlib controls are recorded in
[the representation-aware handoff](../pantograph_backport/compiler_aware_validation/README.md).
The [scope-aware handoff](../pantograph_backport/scope_aware_validation/README.md),
Stage 4 and transactional-resource captures retain their original
validation versions and source/binary identities. Their old application codec
and graph results are not current-client acceptance evidence.
