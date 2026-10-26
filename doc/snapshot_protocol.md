# Retained snapshots: provenance, inspection and certification

Protocol version 2 lets a client keep result states alive and run later
tactics on them directly, instead of rebuilding each goal from its printed
form. It adds what such a client needs: how a transition's goals relate to its
input, a read-only view of obligations a state no longer lists, and a kernel
check of a complete root proof.

`protocol.describe` reports `protocolVersion: 2` together with
`transitionProvenanceVersion: 1`, `inspectionVersion: 1` and
`certificationVersion: 1`. The model S-expression version stays 1, and model
goal serialization is unchanged.

Names below are metavariable and free-variable IDs (`_uniq.N`). They identify
an obligation or local inside one state lineage. They are not stable across
sessions or across a replay of the same tactics, and a client must not persist
them.

## Transition provenance

Every successful `goal.tactic` response carries `transition`:

| Field | Meaning |
| --- | --- |
| `selected` | The input goal the operation ran on |
| `direct` | Unassigned goals the operation produced for `selected`, in the order the tactic returned them, before automatic resumption |
| `introduced` | One list per `direct` goal: its visible locals that `selected` does not have, in context order |
| `siblings` | Input goals other than `selected` that the result still lists |
| `changed` | The siblings whose instantiated target, or a local type or value, differs from the input |
| `closed` | Input goals other than `selected` that the transition assigned |
| `dormant` | Input goals other than `selected` that are unassigned but not listed |
| `extra` | Every other listed goal, such as a reachable hole restored by validation |

`direct`, `siblings` and `extra` partition `goals`. A goal the tactic returned
that was already an input goal counts as a sibling, not as a direct goal. If the
operation leaves `selected` itself open, as `skip` does, `selected` is its own
only direct goal. The
categories come from metavariable identities and assignments in the saved
contexts, never from comparing printed goals.

After `constructor` on `True ∧ True`, both goals are direct. Solving the second
of them gives `selected` = that goal, no direct goals, and the first goal as a
sibling. With `∃ n : Nat, n = 0 ∧ n = 1` split into `?w`, `?a` and `?b`, solving
`?a` with `rfl` assigns the witness: `?w` is closed and `?b` is changed.

## `goal.inspect`

Request `{"stateId", "goals"}`, where `goals` is a nonempty list of distinct
obligation names. The response lists one entry per name, in request order:

| Field | Meaning |
| --- | --- |
| `name` | The obligation |
| `status` | `active` (listed), `pending` (unassigned, not listed), `assigned` (assigned, with unresolved holes), `delayed` (delayed assignment whose pending proof has unresolved holes) or `complete` |
| `goal` | The serialized goal, for `active` and `pending` |
| `holes` | Unassigned metavariables reachable from the instantiated target and locals, or from the instantiated assignment |
| `universeHoles` | Whether a universe metavariable remains |

An obligation is `complete` when its instantiated assignment has no
metavariables, including universe ones. A name the state does not declare is an
`index` error. Inspection changes no state and allocates nothing.

## `goal.certify`

Request `{"stateId"}` with optional `maxHeartbeats` (thousands, as the Lean
option; default 200000). The response is `{version, status, reason?, receipt?}`:

| `status` | Meaning |
| --- | --- |
| `certified` | The kernel accepted the root proof; `receipt` is present |
| `incomplete` | Goals remain, the root is unassigned, or holes remain |
| `rejected` | The proof is not acceptable; `reason` says why |
| `inconclusive` | The kernel ran out of heartbeats, memory or recursion depth, or was interrupted |

The server records the root statement and its universe parameters at
`goal.start`. Certification:

1. requires an empty goal list and an assigned root, then instantiates the root
   assignment and requires it to be free of term and universe metavariables;
2. abstracts the proof over the root's local context natively (assumptions
   become binders, local definitions keep their values) and rejects loose bound
   variables or locals outside that context;
3. checks the proof against the recorded root statement, not the root's
   current type and not any caller-supplied statement;
4. walks every constant the proof reaches, imported ones included, and rejects
   `sorryAx`, unsafe dependencies, missing declarations and axioms that are not
   in the state's trusted environment;
5. rechecks declarations added during the search (auxiliary lemmas, matchers)
   in dependency order on a copy of the trusted environment, then checks the
   root as a theorem (or, for a statement that is not a proposition, as an
   opaque definition) with `Environment.addDeclCore`. The kernel is called
   directly, so `debug.skipKernelTC` cannot skip checking.

Checking works on environment values only. No search state, and not the REPL's
own environment, sees the temporary declaration, and certifying again returns
the same result.

The receipt records the root name, universe parameters, a structural 64-bit
digest of the checked statement and proof (`identity: lean-expr-digest-v1`,
which ignores bound variable names, so a term is identified up to renaming),
an identity of the trusted environment (toolchain commit and imported module
names), the Lean version, the baseline axioms the proof uses and the
auxiliary declarations that were rechecked. It is reproducibility metadata. It
is not a cryptographic proof, and it does not replace rechecking a replayed
proof in a fresh session.

## Tests

`Test/Snapshot.lean` covers nonzero selection, either side of a conjunction
first, identical targets, survivors next to direct goals, introduced locals,
the shared witness (closed and changed siblings, separate alternatives),
inspection of solved and delayed obligations, and rejected inspection requests.
For certification it covers incomplete states, repeated checks, the
conflicting witness, universe-polymorphic roots, reported baseline axioms, a
new axiom, a rechecked auxiliary lemma, new and trusted-basis admissions, an
ill-typed assignment under `debug.skipKernelTC=true`, and a replaced root
statement.
