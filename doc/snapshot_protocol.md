# Retained snapshots: provenance and inspection

Protocol version 2 lets a client keep result states alive and run later
tactics on them directly, instead of rebuilding each goal from its printed
form. It adds what such a client needs: how a transition's goals relate to its
input, and a read-only view of obligations a state no longer lists.

`protocol.describe` reports `protocolVersion: 2` together with
`transitionProvenanceVersion: 1` and `inspectionVersion: 1`. The model S-expression version stays 1, and model
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

## Tests

`Test/Snapshot.lean` covers nonzero selection, either side of a conjunction
first, identical targets, survivors next to direct goals, introduced locals,
the shared witness (closed and changed siblings, separate alternatives),
inspection of solved and delayed obligations, and rejected inspection requests.
