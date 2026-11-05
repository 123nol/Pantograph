# Scope-aware validation: REPL stages 0–2

Implemented locally on `feat/scope-aware-transition-validation` over
`5cab95e132bcdd1d3cb715505d1694ac7bb0e0d6`. The source changes are uncommitted.
The [ownership inventory](../../doc/scope_aware_ownership.md) and
[version-2 contract](../../doc/scope_aware_validation.md) describe the boundary.
`provenance.json` identifies the tested executable and exact source-file hashes.

## Stage 0 evidence

`baseline-diagnostic.json` records the pre-repair conjunction reproduction. It
contains an ordinary assigned metavariable of type `Prop` whose value references
a local absent from its owner and whose identity is outside the diagnostic root
walk. The old validator rejects the transition; the direct snapshot certifier
returns a kernel receipt. `ordinary-lean-baseline.txt` records ordinary Lean's
acceptance of conjunction, disjunction, and the full supplied Finset statement.
Generated names are observations, not assertions in the regression tests.

`baseline-provenance.json` records the initial source and old executable hash.
`old-executable-verification.json` independently matches that executable to the
previous transactional-resource provenance and captures its revision-3,
validation-version-1 descriptor. The binary is preserved locally at
`.lake/verification/repl-transition-validation-v1`, outside Lake's build directory.
That ignored binary is not part of this source change and must be copied before
cleaning or replacing the workspace if a later deployment migration needs it.

The inspected Mathlib directory is a copied source tree inside the application
Git root. A separate Git object database was fetched at exact commit
`29dcec074de168ac2bf835a77ef68bbe069194c5`. All 4,737 tracked Lean/toolchain/manifest
files match that commit, with no extra Mathlib Lean files. The separate gate
repeats this comparison. `mathlib-source-verification.json` records the initial
comparison; the final capture records the repeated comparison.
`compiled-mathlib-identity.json` records an aggregate SHA-256 over 4,760 compiled
Lean files in Mathlib and its dependency builds. This identifies the tested local
compiled contents; it is not the application's environment fingerprint or a
claim of a fresh Mathlib rebuild.

## Implementation

The shared scanner distinguishes strict execution checking from auxiliary
hazard auditing. It follows retained/public obligation owners, original root
metadata, delayed abstraction, pending/synthetic/coercion work, let-rec lifting,
postponed constraints, conversion/calculation state, and closed environment
additions. Local membership precedes memoization; binder depth and assignment
cycles are checked. Unresolved dependency scopes remain checked through assigned
wrappers. Inert records are retained and rechecked whenever they become live.
The auxiliary audit scans retained syntax without advertising scratch holes as
proof goals. Rebuildable Core/Meta caches are cleared; resumable work is retained.

Every REPL allocation path validates before publication. Inspection and
continuation validate newly requested identities. Native operation exports use
the shared transition boundary. A validation integrity error aborts the staged
transaction, emits the existing validation error envelope, and ends the session.
Resource exhaustion preserves the existing structured resource contract.

The certifier checks retained hazards before abstraction can erase unused local
let values. Both root constructors now capture universe parameters from the root
and retained local types/values after assignment instantiation. Certification
instantiates the abstracted statement and value before kernel checking. This
repairs the audited single-root frontend path, which previously lost a universe
parameter occurring only in local types. Kernel certification and the original
trust environment remain mandatory.

Native operation callers now expose an unresolved inferred proposition instead
of hiding that obligation. The migrated regression checks its identity and
context relationships rather than a generated metavariable suffix.

The descriptor advertises `transitionValidationVersion: 2`; successful tactic
metadata uses `execution-closure-and-transition-audit`. Overall protocol version
3 and the existing resource, transaction, model, provenance, inspection, and
certification versions are unchanged. No compatibility fallback was added.

## Verification

Passed on the final build:

- `lake build repl test scope_diagnostic`
- `lake test`: **393 assertions**. This includes the existing safety, snapshot,
  universe, conversion/calculation, serialization, transaction, and certification
  suites together with ownership, residue promotion, pending-work, delayed
  abstraction, hidden-hole, resource, and fatal rollback regressions.
- `python3 scripts/test_scope_aware_validation.py`: **17 core exchanges** with
  no Mathlib source/build dependency.
- `python3 scripts/test_scope_aware_validation.py --mathlib /home/nolawi/new-maths/maths_ai/sexpr_environment/sexpr_environment/mathlib4 --mathlib-reference /tmp/pantograph-mathlib-reference --capture pantograph_backport/scope_aware_validation`:
  **17 core and 29 Mathlib exchanges**. Controls include real `tauto`, the full
  Finset context/universes, incomplete and sibling execution, original-root
  receipts, alternative snapshot reuse, inspection, continuation, frontend
  certification, final deletion, and fatal validation shutdown.
- `lake env python3 scripts/test_transactional_resources.py`: **22 exchanges**,
  preserving real heartbeat recovery, certification exhaustion, compact framing,
  tracing, unusable-session behavior, and a broken output pipe.
- JSON Schema checks of version-2 fixtures and captured validation metadata/error
  envelopes. Version 1, the old scope, false checks, allocation IDs on errors,
  and a recoverable-validation field are rejected.
- `git diff --check`

`capture.json` contains final raw exchanges and the direct snapshot diagnostic.
The copied logs distinguish the ordinary native suite, core executable gate,
Mathlib gate, and transactional-resource harness. Historical revision-1 captures
in other directories remain unchanged.

## Scope and remaining delivery

These results complete the requested REPL work in stages 0–2. They do not claim
standalone-client, application search/RL, Docker, service, or JupyterHub
acceptance. Stages 3–6 must migrate strict client consumers to validation version
2, publish exact source pins, verify the deployment's old executable and complete
artifact chain, and establish the coordinated rollout. The preserved old local
binary does not prove which binary or model/inventory bundle a remote deployment
used. No deployed executable, trained weights, or application bindings changed.
