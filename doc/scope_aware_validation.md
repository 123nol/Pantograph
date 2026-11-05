# Scope-aware transition validation, version 2

The shared validator accepts inert elaboration residue while requiring valid
owners for executable references. A missing local in an orphan assignment does
not establish a dangling reference in the retained proof. It also does not grant
the record an exemption when a later operation makes it executable.

`protocol.describe` reports `transitionValidationVersion: 2`. Successful tactic
responses include exactly:

```json
{"version":2,"scope":"execution-closure-and-transition-audit","checked":true}
```

This object is the `validation` field. Protocol version 3, compact framing,
resource errors, provenance, inspection, and certification keep their existing
versions. [The schema](scope_aware_validation.schema.json) and
[fixtures](scope_aware_validation.fixtures.json) are the strict version-2 contract.
Current client consumers must migrate together; no version-1 fallback exists.

## Ownership and traversal

`ExpressionOwner` identifies the exact local context and traversal scope for an
expression in one retained snapshot. `ValidationPurpose` distinguishes strict
execution checking from auxiliary auditing. The [saved-state inventory](scope_aware_ownership.md)
identifies every root and metadata category using the pinned Lean definitions.

Execution starts from the original root and statement, selected/input/output
obligations, previously published identities, parent, and conversion/calculation
state. It follows assignment dependencies, every owned local type and let value,
and local instances. Pending/synthetic elaboration, coercions, let-rec lifting,
and postponed universe work are also strictly checked under their saved owners.
Those metadata roots do not automatically become new proof goals. Unresolved
holes reachable from the proof closure remain visible; dormant siblings and
conversion placeholders retain their mode semantics.

Local declarations are checked against their context prefix. Free-variable
membership is checked before consulting the visited cache. Metavariable records
have fixed declaration owners; their use sites also check free locals and
unresolved dependency scopes. An assigned wrapper cannot conceal a dependency
whose future assignment could escape the caller's local context. A declaration
in another goal never resolves a missing local in the current owner.

Binder depth increases only inside a lambda, forall, or let body. Metavariable
assignments and local values begin at depth zero. Delayed assignments check
abstraction variables in the pending declaration's context and check the
remaining references against the delayed owner's use context. Ordinary,
delayed, local, and reachable universe cycles fail deterministically. Missing
metavariable/universe declarations, dependencies, and loose executable binders
also fail.

The original root identity, statement, universe parameters, and local-context
identity/types/values cannot be replaced by a transition. The prior snapshot's
trust environment remains the lineage trust basis. New environment declarations
are closed owners rather than expressions borrowing a goal's locals.

## Auxiliary audit and caches

The audit walks all retained metavariable syntax and local contexts, including
changed and newly created records. It also examines retained environment
additions and relevant diagnostic expression syntax. Auditing the retained
records preserves hazard evidence across subsequent transitions without a
persistent exemption list. A missing local in an inert record is recorded as
bounded auxiliary residue. Independent branches still contribute explicit
admission and unsafe evidence. Missing assignment owners, missing delayed
targets, or cycles fail closed.

The validator never reconstructs discarded local values. It never deletes
metavariable records. Completed root certification still succeeds for the
reproduced inert orphan because that orphan contributes no detectable admission
or unsafe dependency.

Derived Core and Meta caches are cleared in the returned snapshot using the
rebuildability established by Lean's cache and restoration APIs. Resumable work
is retained and checked. Historical info trees and diagnostic metadata are not
the incremental tactic cache. Every traversal polls the existing command budget;
there is no separate unbounded recovery scan.

Auxiliary residue diagnostics identify purpose, owner, path, and declaration.
The diagnostic executable captures them independently of protocol stdout.
Generated names are observations, not regression-test assertions.

## Publication, inspection, and certification

The shared allocation helper validates starts, tactic results, continuations,
and frontend obligations before inserting them into the staged table. Native
operation exports use the same transition checks. Internal goal-building helpers
can construct raw intermediate snapshots for composition and negative tests;
production publication always passes validation.

`goal.inspect` strictly checks requested identities and records newly published
obligation metadata within the request transaction. `goal.continue` checks
requested records even if their assignment means they do not become active
goals. Later descendants preserve published identities. Existing inspection and
provenance response representations are unchanged.

Validation failures use a dedicated internal abort, not an ordinary successful
handler return containing an error. The transaction discards staged allocation,
option, environment, message, and freshness changes. It returns the existing
`{"error":"validation","desc":"..."}` envelope with no result IDs, then stops
accepting input and exits nonzero. This is an integrity failure. Ordinary tactic
failures remain ordinary candidate outcomes; safe resource exhaustion retains
its existing rollback envelope.

The certifier checks retained hazards before abstracting the root's locals.
Lean's binding abstraction drops unused let values, so scanning only the
abstracted proof could lose an unused admission. Such a snapshot is refused.
Shared root constructors preserve universe parameters from the instantiated
statement and retained local types/values, including single-root frontend states.
Certification instantiates the abstracted statement and value before checking
closedness. Final dependency scanning and direct kernel checks remain mandatory. An empty
goal list or successful transition never substitutes for a kernel receipt.

## Verification

The ordinary suite has no Mathlib import dependency. Build and run:

```text
lake build repl test scope_diagnostic
lake test
lake env python3 scripts/test_transactional_resources.py
python3 scripts/test_scope_aware_validation.py
```

The separate real-tactic gate requires a Mathlib build and a Git object database
containing commit `29dcec074de168ac2bf835a77ef68bbe069194c5`:

```text
python3 scripts/test_scope_aware_validation.py --mathlib <mathlib-root> --mathlib-reference <reference-git-checkout> --capture pantograph_backport/scope_aware_validation
```

The gate verifies every tracked Lean/toolchain/manifest file against that exact
commit before running ordinary Lean and the executable controls. The reference
can be the Mathlib checkout itself if it has the required Git objects. For a
copied source tree, fetch the pinned commit into a separate reference directory.
No sources or compiled dependencies in the Mathlib build are modified.

The controls cover conjunction, disjunction, the supplied Finset theorem with
its full context, incomplete-to-complete execution, siblings, alternative input
reuse, inspection, cleanup, and kernel receipts. Core regressions cover inert
residue promotion, incompatible owners, delayed abstraction, loose binders,
missing declarations, retained hazards, strict resumable work, resource limits,
and fatal rollback. See [the evidence handoff](../pantograph_backport/scope_aware_validation/README.md).
