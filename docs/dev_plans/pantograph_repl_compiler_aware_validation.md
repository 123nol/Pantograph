# Compiler-aware retained-state validation in the custom Pantograph REPL

## Status and objective

This is a proposed implementation plan for `123nol/Pantograph`. No runtime changes are implemented by this document. Coordinate it with [the standalone-client plan](pantograph_client_compiler_aware_validation.md) and [the application integration plan](mcts_compiler_aware_validation_integration.md).

Accept valid retained transitions that create compiler representations without interpreting those representations as kernel proof expressions. Preserve strict executable dependency checks, auxiliary hazard auditing, transactional resource handling, and original-root kernel certification.

The scope change is explicit: the shared validator must distinguish the representation and provenance of retained environment data. The existing execution-versus-auxiliary distinction alone does not establish which expression grammar applies to an environment entry.

## Baseline and evidence

| Item | Inspected baseline |
| --- | --- |
| Custom REPL | `/home/nolawi/pantograph_fork`, commit `ba2c3dd8383f90b4b5327e31a645a53411f385e4` |
| Standalone client | `053ff67dfc540391100c86e4deada06839904655` |
| Application | `MCTS-AC-branch`, `6f4d94df7343eef07d8843e048aa0c9974d7a8a9` |
| Toolchain | `leanprover/lean4:v4.10.0-rc1` |
| Current contract | Overall protocol 3; transition validation 2; scope `execution-closure-and-transition-audit` |

The JupyterHub traceback reports:

```text
execution owner=declaration _private.0.Nat.pow.match_1.splitter._rarg._cstage2
path=environment audit/declaration-type/binder-type:
Missing proof dependency _obj
```

The call is `goal.tactic` during periodic evaluation through best-first search. The preceding log shows an accepted `simp` result for `True ∧ True`, followed by a QED candidate. It does not identify the command that subsequently fails. Neither final certification of that candidate nor the exact compiler-producing tactic is established by this excerpt.

Inspected code establishes these facts:

- `Pantograph/Validation.lean:auditAuxiliary` enumerates additions using `state.env.constants.foldStage2`, excluding names already in the trusted environment.
- `inspectConstant` calls `Environment.find?`, records `info.isUnsafe`, and traverses the type and optional value of each untrusted declaration using execution validation, including when reached through the auxiliary audit.
- `Pantograph/Certify.lean:certifyRoot` invokes `validateSnapshot` before its separate dependency scan and kernel check. Repairing only `goal.tactic` would leave this second entry point vulnerable.
- The pinned Lean `Environment.lean` distinguishes ordinary constants from code-generator auxiliary names in `extraConstNames` and `const2ModIdx`. Those fields are evidence sources to investigate, not an established classifier for the reported entry.
- `foldStage2` describes the local stage of Lean's persistent map. It must not be interpreted as identifying compiler phase two or as proving that every enumerated declaration is compiler output.

The generated name and `_obj` diagnostic support a compiler-representation hypothesis. The exact source, insertion mechanism, and legal ownership of this entry have not been reproduced or established. Stage 0 is mandatory before exemptions are implemented.

## Design and alternatives

| Approach | Benefit | Cost or correctness problem | Decision |
| --- | --- | --- | --- |
| Ignore `_obj` or names containing `_cstage2` | Small change | Forged or malformed kernel expressions gain the same exemption | Reject |
| Ignore every unsafe or newly generated declaration | Avoids some auxiliary failures | Hides actual unsafe proof dependencies and user-introduced hazards | Reject |
| Disable environment auditing or validate only completed roots | Simplifies traversal | Loses protection for incomplete retained states, local values, and pending execution | Reject |
| Disable compilation globally during search | Might avoid this trigger | Changes tactic execution and leaves the shared validator unable to handle supported representations | Reject as the repair |
| Remove all generated declarations after a tactic | Could reduce retained data | Can invalidate compiler caches, executable functions, or later tactic operations | Reject without a separate lifecycle proof |
| Classify representation using verified compiler/environment provenance, then dispatch to the appropriate audit | Preserves proof checks and valid compilation | Requires native investigation and shared validation changes | Choose |

### Classification and ownership

Introduce a shared classification boundary with three conceptual outcomes:

1. **Kernel declaration:** its type and value obey Lean kernel expression rules. Strictly inspect references, binder scope, universes, and relevant hazards. Compiler-generated declarations that are genuine kernel declarations still belong here.
2. **Compiler representation:** the pinned compiler's authoritative metadata establishes its representation, producing declaration or module, and permitted runtime references. Audit it with those rules. This category does not grant permission to use compiler-only symbols as proof constants.
3. **Unclassified retained data:** provenance is insufficient to justify an alternate grammar. Preserve the integrity failure and record bounded diagnostics.

Use authoritative metadata or a compiler-supported registration boundary. String suffixes, `isUnsafe`, membership in a newly added map segment, or failure of kernel checking are insufficient classifiers individually or in combination without a documented compiler invariant.

Stage 0 must identify the exact supported APIs and their behavior for fresh versus imported compiler data. If the pinned compiler does not expose adequate provenance, stop before implementing relaxed validation. Design and review explicit provenance registration at the actual generation boundary. A required Lean toolchain patch is a separate reviewed scope change, not an implicit addition to this plan.

### Separate dependencies by use

Keep representation classification separate from reachability. Record whether an entry is needed by the kernel proof closure, retained kernel contexts, resumable elaboration/tactic execution, or only retained compiler bookkeeping.

- Kernel proof references must resolve to legal kernel constants. A compiler-only sentinel referenced by a kernel proof remains invalid even if the same sentinel is valid inside a compiler representation.
- Retained kernel local values and auxiliary kernel expressions retain the existing checks for admissions and unsafe dependencies, including unused local let values.
- Compiler runtime support does not become a theorem dependency merely because it is present in the environment. Conversely, compilation provenance must not hide a newly introduced axiom or an unsafe dependency in the proof closure.
- Compiler data that later supplies a kernel expression must cross the strict boundary at that use. Do not persist a name-based exemption across transitions.
- Do not execute arbitrary unsafe code to decide whether an entry is a valid proof dependency.

Define the compiler-data audit from the actual representation contract found in Stage 0. Cover its owner, allowed runtime primitives, dependency resolution, representation well-formedness, and association with generated declarations. Do not claim that checking compiler provenance formally verifies native machine code. Preserve the existing trust policy for tactics that use native computation or introduce additional axioms.

### Shared validator and certifier

Place the classifier and reference-role rules in shared REPL infrastructure, for example a new `Pantograph/DeclarationAudit.lean` module imported by validation and certification. The exact file split follows the discovered API.

Migrate `inspectConstant`, `auditAuxiliary`, executable-root traversal, and `Certify.scanConstant` together. Certification still rebuilds the required kernel dependency closure in a copy of the trusted environment and invokes `Environment.addDeclCore` on the original root statement. Compiler-only entries must not be copied into this kernel dependency environment as theorem declarations.

Memoization must distinguish representation and reference role where their allowed dependencies differ. Classification in a runtime audit must never suppress a later strict proof-reference check. Keep polling, bounded diagnostics, cycle detection, resource-phase reporting, and transaction rollback active throughout classification and auditing.

### Contract decision

Advertise the revised audit boundary explicitly:

```json
{
  "transitionValidationVersion": 3
}
```

Successful validation metadata becomes:

```json
{
  "validation": {
    "version": 3,
    "scope": "execution-closure-and-representation-aware-audit",
    "checked": true
  }
}
```

These are selected fields, not complete envelopes. Overall protocol version remains 3. Transition provenance, model expressions, inspection, certification, and transactional resource schemas retain their versions unless investigation establishes a separate change that requires review.

A version bump makes the changed classification and hazard boundary discoverable before execution. Keeping validation version 2 would reduce migration work but would give different auditing semantics the same advertised contract. Choose explicit versioning and migrate consumers together without a permissive version-2 decoder.

`hasSorry` and `hasUnsafe` continue to describe hazards under the declared validation boundary. Documentation must distinguish kernel proof/retained kernel hazards from legitimate compiler runtime machinery. Genuine validation failures retain their existing terminal error category; no recoverable validation exception is introduced.

## Stage 0: Capture the failure and establish representation provenance

1. Recheck branch revisions and preserve the current executable separately from the new build directory.
2. Capture the actual failing `goal.tactic` command, prior root initialization, preceding commands, options, imports, and toolchain. Use a request/response journal written before command dispatch. Bound log size and keep protocol stdout unchanged.
3. Reproduce with a fresh process and with the preceding successful search history. Determine whether accumulated compiler state is required.
4. Capture the reported entry's `ConstantInfo` kind, safety, type/value representation, environment-map placement, imported-module association, and relevant compiler-extension metadata. Record whether `_obj` is an ordinary constant, compiler primitive, or unresolved data in that representation.
5. Trace the pinned Lean source that creates the entry and the APIs that later consume it. Obtain missing compiler source at the exact toolchain revision if the installed toolchain contains only part of it.
6. Minimize the command sequence. Exercise ordinary Lean independently to establish whether the tactic itself is valid under the same imports and trust policy.
7. Inventory all environment-audit and certification callers, including start, tactic, inspection, conversion, native operations, and final certification.

**Exit gate:** a checked-in native regression reproduces the old failure; a provenance table identifies the representation and APIs. If the data is a genuinely malformed kernel declaration instead, revise this plan to repair its creation rather than exempt it.

## Stage 1: Implement the shared representation boundary

1. Implement the verified classifier and representation-specific audits.
2. Preserve strict validation for all kernel expressions and unresolved classifications.
3. Migrate the validator and certifier callers together, including cache keys and hazard accounting.
4. Keep environment classification state inside snapshot/transaction ownership. Reject, cancel, or roll back without publishing an unchecked allocation or compiler-environment mutation.
5. Retain original-root statement identity and the existing kernel-certification boundary. Empty active goals are insufficient for success.

**Exit gate:** the native reproduction returns a checked transition and certifies the intended root; adversarial proof dependencies still fail. A valid incomplete transition remains usable by subsequent tactics and inspection.

## Stage 2: Publish validation version 3 and strengthen regressions

Migrate the descriptor, response producers, contract documents, current fixture generators, and native clients in this repository. Preserve historical captures with their original versions and hashes.

| Regression | Required result |
| --- | --- |
| Exact minimized failure, with fresh and warmed execution history | Accepted transition and original-root kernel certificate |
| Compiler-generating operation followed by another tactic, inspection, and certification | Consistent classification at every entry point |
| Real auxiliary kernel declaration used in the proof | Strict dependency checks and successful kernel reconstruction |
| A normal declaration merely named with `_cstage2` | No representation exemption |
| Missing constant or `_obj` in an ordinary kernel expression | Terminal validation failure |
| Compiler-only entry referenced from the root proof | Rejected as a kernel dependency |
| Unsafe proof dependency, `sorry`, new untrusted axiom, or unsafe retained kernel let value | Existing rejection/hazard policy preserved |
| Malformed compiler data, missing provenance, or invalid runtime reference | Integrity failure rather than accepted residue |
| Same entry first audited as runtime data, then reached through a kernel proof reference | Strict proof check is not suppressed by memoization |
| Heartbeat, allocation failure, cancellation, or validation failure during the audit | Existing structured resource/terminal behavior, rollback, and ownership guarantees |
| Existing scope-aware `tauto`, sibling replay, delayed-assignment, and hidden-goal controls | Continue passing without intermediate reconstruction |

Add a `True ∧ True` search-history control, but do not call that alone a reproduction of the reported compiler failure. Generated numeric names are observations, not stable assertions.

**Verification:** run the ordinary native suite, a separately declared Mathlib gate, and package-independent raw protocol captures. Mark skipped or unexecuted native controls explicitly.

## Stage 3: Deliver the companion and hand off

- Commit the repaired source, native tests, contract documentation, and a focused handoff.
- Record full source/toolchain/Mathlib revisions, executable digest, source hashes, raw captures, exact reproduction commands, and test results.
- Supply the standalone client with the immutable REPL commit and companion patch provenance. Do not use a moving branch as deployment evidence.
- Record the old executable digest and preserve the binary for deployment rebinding.
- Coordinate the client release before application dependency migration. Do not point production at the new descriptor while its installed client only accepts validation version 2.

## Completion criteria

The exact failure has a native regression, accepted results are representation-audited, genuine kernel dependency failures remain terminal, and final success requires a certificate for the original root. Classification uses established provenance rather than symbol spelling. Client and application consumers migrate through the companion plans.
