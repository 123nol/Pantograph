# Saved-state ownership inventory for Lean 4.10.0-rc1

This inventory applies to Lean revision
`3b58e0649156610ce3aeed4f7b5c652340c668d4` and the custom REPL based on
`5cab95e132bcdd1d3cb715505d1694ac7bb0e0d6`.

An expression owner identifies the retained snapshot and its exact local context.
Binder depth is tracked separately. Metavariable declarations own their types,
local declarations, local instances, and ordinary assignments. A closed
environment declaration has an empty local context. Delayed-assignment variables
belong to the pending declaration's context and are abstracted from its value.

| Retained field or operation | Owner and validation treatment |
| --- | --- |
| Original root, root type, root universe parameters | Strict roots under the original root declaration; anonymous frontend states contain obligations rather than a certifiable theorem |
| Input/output active goals, selected goal, parent | Strict roots; local types and let values are checked even when the assignment does not use them |
| Published goal/provenance identities | Retained explicitly across descendants; remain strict roots after assignment or dormancy |
| `convMVar?` | Strict roots for RHS metavariable, equation goal, and dormant goals; unresolved RHS is not advertised as an ordinary tactic obligation |
| `calcPrevRhs?` | Strict expression under the recorded remainder goal's local context |
| `MetavarContext.eAssignment` | Reachable assignments are strict; other stored syntax is audited for hazards and residue |
| `MetavarContext.dAssignment` | Follow pending target and abstraction variables in the pending context; validate the abstraction against the delayed owner's context; detect cycles |
| `MetavarContext.lAssignment`, `lDepth` | Follow reachable universe assignments with cycle detection; unassigned declared universes remain incomplete |
| `Term.State.pendingMVars` and `syntheticMVars` | Strict resumable roots, including coercion expressions under the synthetic owner's context |
| `Term.State.letRecsToLift` | Strict expressions under each saved `lctx`, with saved local instances and metavariable; syntax/attributes/termination hints are source data, not saved elaborated expressions |
| `Meta.State.postponed` | Strict universe constraints and saved `DefEqContext` expressions/local instances under their saved context |
| `Term.State.mvarErrorInfos`, `mvarArgNames` | Diagnostic metadata, not resumable work; implicit-argument expression syntax is audited; actual pending owners are independently strict |
| `Meta.State.diag` | Counters and diagnostic failure descriptions; stored failure-expression syntax is audited, not promoted to proof obligations |
| `Meta.State.zetaDeltaFVarIds` | Tracking identities used by `getZetaDeltaFVarIds`/`resetZetaDeltaFVarIds`; no expression values or resumable callback; does not resolve a free variable in another owner |
| `Core.State.messages`, trace state | Historical diagnostics; protocol messages are rendered before retention; never sources of execution assignments |
| `Core.State.infoState` | Historical info trees and their diagnostic contexts; not the incremental tactic cache, and not used to resume retained commands |
| Environment additions | Closed declaration owners; new declarations and dependencies are audited even when the root does not use them |
| `goal.inspect`, `goal.continue` with caller-supplied names | Requested identities receive fresh strict validation before inspection/resumption and become published roots when exposed; guesses cannot grant an inert record an exemption |
| `goal.print`, expression serialization, certification | Use the already validated root/parent/goal closure and existing snapshot isolation; certification remains the final kernel boundary |

`Elab.Tactic.SavedState` contains only `Term.SavedState` and the tactic goal list.
`Term.SavedState` contains `Meta.SavedState` and `Term.State`.
`Meta.SavedState` contains `Core.SavedState` and `Meta.State`.
No incremental `Tactic.Cache` is part of this hierarchy. Each retained tactic
starts with a fresh tactic reader context and the shared condensed term context.
The historical info tree therefore does not reactivate an old tactic snapshot.
Native tactic code can deliberately read arbitrary stored records; any resulting
executable expression must pass the next transition's strict traversal.

## Derived caches

`Core.Cache` stores instantiated types/values of environment constants.
`Meta.Cache` stores type inference, function information, typeclass synthesis,
weak-head normalization, and definitional-equality results. These are derived
results, not pending elaboration steps. The pinned `Core` environment instance
and `Meta` environment instance clear them when environments change;
`Meta.savingCache` saves/restores the complete cache. `Meta.SavedState.restore`
restores the metavariable context and postponed work without restoring caches.
These APIs establish that empty caches are valid and rebuildable.

The shared validator returns snapshots with empty Core/Meta derived caches, and
snapshot restoration uses those normalized caches. It never deletes metavariable
declarations or assignments. Pending/synthetic/let-rec/postponed work is retained
and strictly validated rather than cleared.

## Baseline evidence and safety behavior

`Test/ScopeDiagnostic.lean` imports Mathlib only at runtime. Its baseline capture
shows an ordinary assigned metavariable of type `Prop` with a local reference
absent from its owner. The record is outside the diagnostic root dependency
walk. The old validator rejects it while the direct certifier returns a receipt.
This walk is reproduction evidence, not a substitute for the inventory above.
Generated names in captures are observations; tests assert relationships.

Before the repair, the core safety tests require admissions and unsafe constants
to set hazard flags, hidden root/local-value/delayed holes to remain goals,
coupled sibling admissions to remain detectable, malformed assignments/cycles to
reject, failed tactics to preserve snapshots, and final certification to reject
invalid proofs or unresolved expression/universe holes. These expectations remain.

The old local executable was copied before rebuilding and its hash is recorded
in `pantograph_backport/scope_aware_validation/baseline-provenance.json`.
Its availability does not establish the identity of a deployed JupyterHub binary
or the application's checkpoint/inventory bundle. Deployment artifact migration
belongs to the application stages and is outside this REPL-only change.

## Universe ownership after the constructor audit

Both root constructors collect universe parameters from the instantiated root
statement and every retained local type/value. A parameter can occur only in a
local type even when the root target itself is a free variable. Single-root
frontend snapshots therefore retain that parameter for certification. Multiple
frontend obligations still use an anonymous aggregate root and cannot receive a
single theorem certificate. The certifier instantiates the abstracted statement
and proof under the saved metavariable context before checking closedness and
calling the kernel. Unresolved universes still prevent certification.
