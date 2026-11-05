# Scope-aware Pantograph transition validation and deployment migration

## Status and objective

This is an implementation plan for coordinated changes to the custom Lean REPL, the standalone Python client, and the Mathematics-ai-atp application. REPL stages 0–2 are implemented locally on `feat/scope-aware-transition-validation`.
The [ownership inventory](../../doc/scope_aware_ownership.md),
[version-2 contract](../../doc/scope_aware_validation.md), and
[native evidence handoff](../../pantograph_backport/scope_aware_validation/README.md)
record the implementation. Client/application/deployment stages 3–6 remain outside
this REPL-only change.

The objective is to accept valid tactics such as `tauto` when Lean leaves auxiliary elaboration records outside the executable proof, while continuing to detect invalid executable references, hidden obligations, `sorry`, and unsafe dependencies. A successful search must still replay one compatible proof and obtain the existing kernel certificate for its original root statement.

The scope change is explicit: validation must understand expression ownership and retained execution state. Every record in Lean's metavariable context is not necessarily a standalone proof expression that is well scoped under its metavariable declaration's original local context.

The implementation must repair the shared validator. It must not blacklist `tauto`, reconstruct intermediate goals, ignore all missing declarations, or convert protocol-integrity failures into ordinary tactic rejections.

## Verified starting points

| Component | Inspected checkout | Inspected revision |
| --- | --- | --- |
| Application | `/home/nolawi/new-maths`, `MCTS-AC-branch` | `f1eb8ca` |
| Custom REPL | `/home/nolawi/pantograph_fork`, `client_centric_repo` | `5cab95e132bcdd1d3cb715505d1694ac7bb0e0d6` |
| Standalone client | `/home/nolawi/Pantograph-Client`, `main` | `3300096484d95af070f2494eb42f5ab03a66450a` |
| Native Mathlib project | `/home/nolawi/new-maths/maths_ai/sexpr_environment/sexpr_environment/mathlib4` | `29dcec074de168ac2bf835a77ef68bbe069194c5` |

The tested Lean version is `4.10.0-rc1`, Lean revision `3b58e0649156610ce3aeed4f7b5c652340c668d4`. Protocol version 3 and the transactional resource-error contract are already deployed in the inspected sources.

Recheck the repository revisions and worktrees before implementation. New work must preserve the transactional resource handling, retained snapshot ownership, replay scheduling, and certification changes already present.

## Reproduction and established mechanism

The JupyterHub failure occurs during `goal.tactic`, before the application adopts a tactic result:

```json
{
  "error": "validation",
  "desc": "Missing local declaration _uniq.299948"
}
```

The selected tactic is `tauto`. The reported declaration is absent from the selected goal's exported locals. That fact alone does not establish whether the declaration belongs to an invalid proof or to discarded elaboration work.

Native tests against the inspected REPL reproduce the failure on this smaller statement:

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  tauto
```

Here `p` and `q` are arbitrary propositions in the theorem's local context. In the REPL reproduction, start the expression `∀ (p q : Prop), p ∧ q → q ∧ p`, introduce `p` and `q`, and apply `tauto` to the remaining goal.

Ordinary Lean also accepts the user's supplied statement:

```lean
universe u_1 u_2 u_3

example (α : Type u_1) (β : Type u_2) (γ : Type u_3)
    [DecidableEq α] (s t u v : Finset α) (a b : α) :
    a ∉ s → ((∀ a ∈ t, a ∉ s) ↔ ∀ ⦃a : α⦄, a ∈ s → a ∉ t) := by
  tauto
```

In this reproduction, `α`, `β`, and `γ` are types in the declared universes; `s`, `t`, `u`, and `v` are finite sets of elements of `α`; and `a` and `b` are elements of `α`. The extra declarations preserve the local context supplied with the failing run.

The following observations distinguish the defect from a malformed starting theorem:

1. `Pantograph.Validation.validateTransition` inspects the selected goal and active goals, then inspects every changed ordinary assignment, changed delayed assignment, newly created context, and pending metavariable.
2. Its free-variable lookup uses the owner metavariable's recorded local context. A failed lookup immediately rejects the entire transition.
3. A direct native snapshot diagnostic reproduces rejection on a changed assignment whose type is `Prop` and whose value references a local declaration absent from the retained contexts.
4. In that diagnostic, the offending assigned metavariable is not reachable from the root through the traversed declaration types, local types and values, ordinary assignments, and delayed-assignment targets.
5. The existing certifier accepts the completed root from that same diagnostic snapshot. Ordinary Lean accepts the theorem independently.

The diagnostic's root-reachability walk is evidence about this reproduction. It is not yet a complete specification of all data an incomplete retained snapshot can use. Siblings, deferred elaboration, conversion state, and execution caches require the broader audit below.

Generated `_uniq` names vary with execution history. Tests must identify ownership and reachability relationships, not assert particular numeric suffixes.

## Architectural decision and alternatives

| Approach | Benefit | Cost or defect | Decision |
| --- | --- | --- | --- |
| Disable `tauto` or catch the protocol exception in search | Small immediate change | Other tactics can expose the same shared defect; valid candidates disappear; invalid state may be concealed | Reject |
| Look up missing locals in the union of every goal's local contexts | May resolve some names | A declaration existing elsewhere does not make it legal in the expression's owning context | Reject |
| Ignore every missing local reference | Accepts the reproduction | Also accepts genuinely dangling references in executable proofs and obligations | Reject |
| Validate only a fully instantiated root | Simple final-proof boundary | Incomplete searches still need valid siblings, hidden obligations, retained local values, and pending work; existing transition checks would be lost | Reject as a transition validator |
| Delete every unreachable metavariable record | Could reduce retained memory | Saved elaborator caches, public historical obligations, and deferred work may reference records omitted by an incomplete traversal | Do not use as the initial repair |
| Separate strict execution validation from an auxiliary transition audit | Follows actual ownership; preserves live-state checks and auxiliary hazard detection | Requires a complete root inventory, context-aware traversal, and stronger regressions | Choose |

The chosen design preserves the existing final kernel-certification boundary. Transition validation determines whether a snapshot can safely enter continued execution; it does not itself certify the theorem.

## Shared validation architecture

### Ownership and the executable dependency closure

An expression owner identifies the saved state, metavariable declaration or closed environment declaration, and local context in which an expression is interpreted. Bound-variable depth belongs to that traversal position. It is distinct from the identity of a free local declaration.

The executable dependency closure is the transitive set of expressions and declarations required by retained execution and public inspection operations. Build an explicit inventory of its roots rather than treating every saved assignment as a root.

The inventory must cover:

- The original root metavariable, root type, and applicable universe information.
- The selected input obligation, the input and output active goals, and retained sibling obligations whose assignment or status can affect replay.
- Local declaration types and let values in those obligations' contexts, including declarations unused by the final proof.
- Ordinary assignments and delayed assignments reachable from those roots, using Lean's owner and substitution rules for delayed assignments.
- Pending and synthetic obligations, postponed elaboration work, and any other saved elaborator data that can resume computation.
- Conversion and calculation state, including dormant goals and saved expressions maintained outside the ordinary active-goal list.
- Previously published obligation identities that inspection or replay may still query in this snapshot.
- Saved caches or environment additions that can supply expressions to later execution. Inspect the exact Lean version's saved-state fields rather than assuming caches are irrelevant.

Derived caches may be cleared only where Lean's API establishes that rebuilding them is semantically valid. Otherwise their retained references must participate in the root inventory. Do not erase arbitrary metavariable records to make the reproduction pass.

For executable expressions, a missing free-variable owner, missing metavariable declaration, illegal loose bound variable, cyclic assignment, or missing dependency is an integrity failure. Context membership must be checked before using a memoized traversal result. Never resolve a free variable by finding a same-named declaration in an unrelated context.

### Strict checking and the auxiliary audit

Use two explicit traversal purposes rather than overloading the existing `track : Bool` flag:

1. **Execution checking:** establish well-scoped references for executable expressions, inspect their trust dependencies, and identify unresolved obligations that must remain visible to search.
2. **Auxiliary auditing:** inspect changed assignments, new retained contexts, and relevant environment additions for detectable `sorry` and unsafe dependencies without assuming that inert elaboration residue is an executable proof.

An auxiliary record may be classified as inert only after proving it is outside the complete executable dependency closure and outside saved work that can resume. A missing local reference within such a record is recorded as auxiliary residue, rather than interpreted as a dangling reference in the root proof.

The audit must still examine stored expression syntax and any declarations with established owners. It must detect explicit `sorry` and unsafe constants in changed records and retained local let values. An unresolved owner must not cause the audit to skip independent expression branches.

Do not claim to recover discarded local declaration values that Lean no longer stores. The contract concerns executable state and hazards inspectable in the retained transition. If ownership cannot be established for data that may still influence execution, fail closed. Such data is not inert residue.

If a later tactic makes a previously inert record executable, validate it under the new transition's closure. Earlier classification must not exempt it from future checks.

Keep hazard evidence separate from executable obligations. An unresolved scratch metavariable does not automatically become a new proof goal. A reachable unresolved obligation must not disappear because its selected parent has been assigned.

### Traversal state and diagnostics

Replace context-insensitive visited keys with keys or traversal structure that account for owner, checking purpose, and bound-variable depth where relevant. In particular, checking a free-variable identity in one goal must not suppress membership checking in another goal.

Retain cycle detection for ordinary and delayed assignments. Make traversal work subject to the existing command heartbeat and transaction budgets. Do not introduce an unbounded second scan after a resource limit has been reached.

Diagnostics should identify the validation purpose, expression owner, dependency path, and failing declaration identity. These diagnostics belong in captured error data or stderr. Protocol stdout must remain one structured response per command.

### Protocol contract

Make the changed validation boundary explicit:

```json
{
  "transitionValidationVersion": 2
}
```

Successful tactic responses must carry:

```json
{
  "validation": {
    "version": 2,
    "scope": "execution-closure-and-transition-audit",
    "checked": true
  }
}
```

These are selected fields, not complete response envelopes. Overall protocol version 3, resource errors, transition provenance, inspection, and certification remain at their existing versions unless implementing the audit uncovers a separate required wire change.

Version 2 distinguishes this explicit validation boundary from the current unqualified scan of changed expressions. Migrate the client and all current application consumers together. Do not add a permissive version-1 decoder or an option that disables the new checks.

Genuine invalid-state validation remains a protocol-integrity failure. This plan does not introduce a recoverable validation exception. Valid `tauto` should return the ordinary successful tactic response; a real dangling executable reference must still retire the affected client session.

## Stage 0: Capture regressions and complete the ownership inventory

**Repositories:** REPL primarily; application for deployment requirements.

**Work:**

- Preserve the minimal conjunction reproduction, disjunction reproduction, and supplied Finset statement as source-controlled tests or test inputs.
- Add a native diagnostic that records the failing expression's owner, context membership, assignment kind, and dependency path. Avoid assuming a stable generated name.
- Compare the direct Lean result, current validator result, and direct snapshot certifier result. The diagnostic use of the certifier does not bypass production validation.
- Inspect `GoalState`, `Elab.Tactic.SavedState`, `MetavarContext`, conversion/calculation fields, and every public inspection operation for executable or published references outside the root proof.
- Document which caches are derived and which saved records can resume computation. Record the Lean APIs supporting that classification.
- Record the existing transition safety tests and their expected flags or rejection behavior before changing them.
- Capture the existing artifact chain and determine whether the old REPL binary is available for an independently verified deployment migration.

**Primary files:** `Pantograph/Validation.lean`, `Pantograph/Goal.lean`, `Pantograph/Repl.lean`, `Pantograph/Certify.lean`, `Test/Validation.lean`, and native Mathlib test support.

**Exit gate:** reproduce the defect and complete the root/owner table. Do not proceed with a root-only traversal while saved-state owners remain unaccounted for.

## Stage 1: Implement the shared REPL validation repair

**Repository:** REPL.

**Work:**

- Introduce explicit owner descriptors and validation purposes in the shared scanner.
- Compute the executable dependency closure from the audited root inventory. Preserve the local context belonging to each expression and the substitution semantics of delayed assignments.
- Validate executable references strictly, including bound-variable depth and context-sensitive visited behavior.
- Audit changed auxiliary expressions and retained contexts separately. Classify the reproduced orphan assignment as inert only after the full ownership test succeeds.
- Preserve accurate `hasSorry` and `hasUnsafe` evidence for retained transition hazards. Keep newly introduced local let values and changed coupled sibling assignments covered.
- Preserve hidden-goal recovery and conversion-specific dormant-goal behavior. Do not append scratch elaboration holes to the active goal list.
- Revalidate inert records if future transitions make them executable. Avoid persisting a broad exemption list.
- Audit every transition entry point that saves state, not only the tactic spelling `tauto`.
- Ensure a validation failure cannot publish a result allocation or commit staged changes. Audit the current transaction path where returning an error envelope is otherwise a successful handler return. Preserve a safely restored pre-command state or terminate the session; do not accept subsequent commands against unverified staged state.
- Emit the version-2 capability and successful validation metadata consistently.

**Exit gate:** valid reproductions return checked transitions; injected executable dangling references still fail; no allocation or environment mutation escapes a rejected transition.

## Stage 2: Establish native REPL safety and certification coverage

**Repository:** REPL, with a separate native Mathlib test gate where required.

The core test suite must not silently acquire an undeclared Mathlib dependency. Keep a small synthetic residue regression in the ordinary suite and run real `tauto` controls against the pinned Mathlib project.

| Case | Required outcome |
| --- | --- |
| Conjunction and disjunction examples using `tauto` | Checked transition and kernel-certified original root |
| Supplied Finset theorem with its full context | Checked transition and kernel-certified original root |
| Valid incomplete tactic followed by a later tactic | Returned state remains usable; final root certifies |
| Several subgoals with shared assignments | Sibling updates and hidden obligations remain inspectable and correctly reported |
| Conversion, calculation, and delayed assignment | Existing goal-mode and ownership behavior is preserved |
| Dangling free variable reachable from a proof or live local value | Integrity failure, no successful allocation |
| Same free-variable identity encountered under incompatible contexts | Context error is not hidden by the visited cache |
| Inert record becomes reachable later | Fresh strict validation applies; invalid ownership fails |
| Missing metavariable, delayed target, assignment cycle, or loose bound variable | Deterministic integrity failure |
| Reachable unassigned proof or universe obligation | Incomplete state or certification refusal, never certified success |
| Explicit or nested `sorry`, unused retained local admission, unsafe dependency | Existing hazard flags/rejection and certification refusal remain effective |
| Coupled sibling assignment containing an admission | Existing negative test remains effective |
| Resource exhaustion during closure construction or auxiliary audit | Existing structured resource outcome and transaction semantics |
| Candidate failure and sibling reuse | Input snapshot remains isolated and valid |

Inspect full certificate results, not only an empty active-goal list. Test immediate and subsequent snapshot inspection, deletion, and alternative execution. Verify stdout framing and absence of leaked allocations or temporary environment declarations.

**Exit gate:** the existing validation, snapshot, contract, transaction, and certification suites pass together with the real Mathlib regressions. Record executable and source hashes for the tested build.

## Stage 3: Update the standalone client's strict contract and compatibility evidence

**Repository:** Pantograph-Client.

**Work:**

- Require `transitionValidationVersion: 2` during startup capability validation.
- Update typed transition-validation decoding to require version 2, the exact new scope, and `checked: true`.
- Migrate successful mock responses, contract fixtures, examples, and native tests. Keep historical captures explicitly historical rather than rewriting evidence of previous binaries.
- Refresh the compatibility source pin, source hashes, executable provenance, and captures against the tested REPL commit.
- Confirm that valid `tauto` transitions return an owned result, can be inspected or continued, and are released normally at scope exit.
- Confirm that a genuine validation error still closes the client as a protocol-integrity failure. Do not catch arbitrary `PantographProtocolError` as a candidate rejection.
- Retain allocation registration and cleanup if response validation, cancellation, or subsequent inspection fails. Reject stale, copied, cross-scope, and cross-session handles as before.
- Preserve resource-error decoding and recovery, including the version-3 command transaction contract.
- Run package tests from both the checkout and built distribution contents where the existing packaging checks require them.

**Primary files:** `src/pantograph_async/protocol.py`, native and protocol tests, compatibility manifests/captures, and the package's installation/compatibility documentation.

**Exit gate:** client startup rejects mismatched validation capabilities, accepts the new checked response, and passes native lifecycle/certification tests against the exact REPL build. Publish an exact client commit for application integration.

## Stage 4: Migrate application consumers and search regressions

**Repository:** Mathematics-ai-atp, initially `MCTS-AC-branch`.

**Work:**

- Pin the tested standalone client commit in `pyproject.toml`, regenerate `uv.lock`, and update generated requirement/Conda installation inputs through their normal generation process.
- Update Docker/provisioning REPL pins to the full tested REPL commit and retain the toolchain/Mathlib pairing.
- Migrate every current validation fixture, typed constructor, handshake assertion, fake client, and diagnostic. Preserve the historical fixture chain and refresh current source-lineage evidence.
- Keep the existing adapter, retained executor, allocation registry, and replay engine as the shared paths. Valid tactics need no new application exception category.
- Test both PUCT and best-first search with controlled proposals containing `tauto`. Search must adopt the checked state, compose/replay it when needed, and report success only after kernel certification.
- Add a multi-step and a multi-goal case so the test does not merely certify a one-step theorem in isolation.
- Verify RL collection accepts the valid result normally. Genuine integrity failures must not become negative argument/tactic labels or ordinary resource outcomes.
- Exercise evaluation and the service runtime through the same installed client and retained execution path.
- Preserve graph normalization, local declaration identities, model inputs, policy mode consistency, and resource accounting. This repair does not authorize changes to those contracts.
- Audit other in-repository callers of the installed client, including diagnostics and setup tools. Record a corresponding coordinated migration for AC-branch before updating its client dependency; do not introduce a decoder accepting both versions in shared code.

**Likely application areas:** `pantograph_adapter.py`, retained execution/replay tests, owned-client migration and source-lineage tests, native search tests, installation inputs, Docker setup, and deployment documentation. Change runtime adapter code only where the actual version migration requires it.

**Exit gate:** both search modes complete the regression proofs with certificates, lifecycle tests pass, and protocol failures remain fatal rather than entering learning as rejected actions.

## Stage 5: Refresh deployment bindings without discarding trained weights

**Repository:** application deployment tooling and shared artifact-validation helpers.

### Why deployment changes are required

The application's `environment_fingerprint` hashes imports, toolchain/lock information, the REPL executable, and compiled Lean artifacts. Rebuilding only the REPL changes that fingerprint.

The declaration inventory stores that identity. The index deployment manifest binds to the inventory's environment; the query manifest binds to the index deployment; and the version-4 action checkpoint binds to the retrieval deployment. Updating only `pantograph_repl` therefore produces the environment mismatch already observed in JupyterHub.

Do not manually replace the environment string in JSON files. Do not run the raw supervised-to-actor-critic converter on an RL-trained model to solve this problem. That converter initializes a critic and is not a deployment migration for already learned actor-critic weights.

### Chosen migration route

Add one validated offline bundle-migration operation, for example `scripts/rebind_source_aware_environment.py`, using the shared manifest, hashing, checkpoint, and inventory helpers. Refactor those helpers where needed instead of duplicating their checks in a one-off script.

Its inputs are the complete old deployment bundle, its existing version-4 actor-critic checkpoint, the exact prepared metadata and corpus, the old REPL identity evidence, the new REPL/source root/imports, and a new output directory.

The operation must:

1. Verify the old checkpoint and all old retrieval/query/index/inventory bindings before making replacements.
2. Establish that the planned migration changes the REPL build while preserving the imported compiled library, toolchain, import list, prepared representation, retrieval tensors, lemma rows/names, and corpus. Reproduce the old fingerprint with the old executable or use independently verifiable component evidence recorded with the old deployment. A single unexplained old hash is insufficient evidence.
3. Generate the new declaration inventory through the real Lean environment, preserving explicit exclusions. Compare declaration availability and abort if the assumed binary-only migration is not established.
4. Write a new index deployment manifest and query pairing while preserving the index contents, embeddings, tokenizer, query weights, and original retrieval training provenance.
5. Write a new checkpoint deployment binding through the existing checkpoint builder. Preserve every model tensor, including the critic and any trained residual or argument heads. Preserve vocabularies and graph metadata.
6. Treat the output as a fresh-run warm start. Do not silently carry optimizer state, imitation queues, best-score incumbents, or exact-resume claims across an environment change. Preserve the original checkpoint separately.
7. Record old/new identities, source revisions, hashes, validation-contract versions, and tensor-equality verification in a migration receipt.
8. Stage output in a temporary directory and publish only after validation succeeds. Refuse overwriting an existing bundle. Preserve containment rules enforced by the artifact loader; external symlinks must not bypass hash validation.

The tensor-preservation assertion compares names, shapes, dtypes, and exact contents of all model state entries. It is not enough to compare the actor head alone.

If the old executable or adequate component provenance is unavailable, stop this narrow migration. Produce a freshly verified deployment using the original matched retriever/index/corpus and explicit source provenance; do not claim that the old environment has been proved equivalent. The model may be transferred only through an explicitly validated warm-start export that preserves its tensors and establishes all new bindings.

The existing export commands remain useful for a first deployment. They are not a substitute for preserving the learned model state during this migration. Broader Mathlib, corpus, vocabulary, or retrieval-model changes require their own validated deployment rather than a permissive override flag.

### Verification and resume behavior

- Test refusal of a changed corpus, changed embedding row order, missing compiled dependency, mismatched tokenizer, altered prepared metadata, tampered old manifest, and missing provenance.
- Test atomic failure and existing-output protection.
- Load the new bundle through the normal candidate provider and strict checkpoint loader against the new executable.
- Assert exact preservation of model tensors and unchanged model predictions on fixed input graphs/candidate pools.
- Verify that a changed retrieval binding prevents restoring incompatible saved pools and exact-run state. Improve the diagnostic if existing model-spec or pool checks do not explain the required fresh run.

**Exit gate:** a new validated bundle starts with the repaired REPL and the same learned model tensors. The old bundle remains intact, and no environment check has been disabled.

## Stage 6: Coordinated rollout and JupyterHub acceptance

**Dependencies:** stages 0–2 establish the REPL; stage 3 establishes the client; stages 4–5 establish the application and artifacts. Final acceptance requires the matched set.

1. Merge the tested REPL repair and record its full commit. Build it in a separate checkout or output location so the old executable remains available for identity verification.
2. Merge the client contract/compatibility update pointing to that REPL revision. Record the exact client commit.
3. Integrate application pins, fixture migration, deployment tooling, and tests. Update each deployment consumer as a matched set.
4. In JupyterHub, activate the intended Conda environment and install the exact pinned client through that environment's `python -m pip`. Verify the imported module path and package provenance before testing.
5. Build the repaired REPL with the matching Lean toolchain. Keep the current Mathlib source root only after verifying its compiled contents and imports satisfy the planned migration.
6. Generate a fresh deployment bundle. Update the trial configuration's checkpoint, inventory, query, index, and REPL paths to that bundle/build. Keep the old configuration and artifacts for rollback.
7. Run the minimal conjunction and supplied Finset native controls. Require checked version-2 responses and kernel certification.
8. Run short controlled trials for PUCT and best-first search, then a bounded dataset trial. Confirm clean snapshot teardown, unchanged resource handling, and no missing-local protocol errors on the captured examples.
9. Run CPU service/container smoke coverage, including readiness and a certified `/prove` result, using the same pinned pair and mounted bundle. Exercise the GPU trial separately when available.

The original remote Mathlib root is `/home/jovyan/yonatan/Mathematics-ai-atp/maths_ai/_support_files/sexpr_environment/mathlib4`. The currently reported transactional REPL is `/home/jovyan/Pantograph-transactional/.lake/build/bin/repl`. These are deployment inputs to verify, not assumptions that a newly built binary has the old fingerprint.

Rollback restores the previous client, REPL, application pins/configuration, and artifact bundle together. Do not keep the new binary with old inventory metadata or allow mixed validation versions to pass startup.

## Completion criteria

- Valid `tauto` on the reported statement and smaller controls produces checked transitions and kernel-certified proofs.
- Missing executable references, unsafe dependencies, admissions, hidden obligations, and cyclic assignments retain explicit negative coverage.
- Incomplete retained snapshots remain usable across sibling execution, replay, inspection, and cleanup.
- Auxiliary residue classification is justified by an audited dependency inventory and is re-evaluated on later transitions.
- The REPL emits one framed response, and validation failure/resource exhaustion cannot leak staged state.
- The client enforces the new validation contract and preserves allocation ownership on every outcome.
- PUCT, best-first, evaluation, RL collection, and service proving use the shared repaired path.
- Deployment migration preserves all learned tensors and passes normal environment/artifact verification.
- Merge and deployment instructions identify the exact tested REPL/client/application revisions and explicitly distinguish a fresh warm start from exact run resumption.

Architecture was explicitly verified before implementation. The completed REPL inventory and native evidence are linked above. Stages 3–6 remain pending in their respective repositories; the full coordinated rollout is not complete.
