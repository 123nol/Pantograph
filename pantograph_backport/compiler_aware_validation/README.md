# Representation-aware validation evidence

Baseline: `client_centric_repo` at `ba2c3dd8383f90b4b5327e31a645a53411f385e4`,
toolchain `leanprover/lean4:v4.10.0-rc1`. The contract is in
[compiler_aware_validation.md](../../doc/compiler_aware_validation.md).

## Reproduction

`baseline-reproduction.json` holds raw exchanges from the baseline executable
(sha256 `a7b420e0915c4e08efcf594cd5b7bd00ca16a70b2b6502aa51c70ad0fd3d95f4`) with
only `Init` imported:

- fresh process: `intro m n`, then `unfold Nat.pow`;
- warmed process: `simp` on `True ∧ True` (certified), then `intro m n` and
  `simp only [Nat.pow]` on a second root.

Both end with the reported error, byte for byte, and the process exits:

```text
execution owner=declaration _private.0.Nat.pow.match_1.splitter._rarg._cstage2 path=environment audit/declaration-type/binder-type: Missing proof dependency _obj
```

Accumulated compiler state is not required. The tactic itself is valid Lean:
the same sequences succeed with the repaired executable and the resulting proof
is kernel-certified.

## Provenance

- `provenance-core.json`: `compiler_diagnostic Init`. For each compiler-producing
  case, every untrusted environment entry with its kind, safety, IR registration
  for the entry and its owner, and unresolved references. `unfold Nat.pow` adds
  the splitter (a safe kernel definition with IR), its equation theorems, and
  three stage entries:

  | Entry | Form | Owner | Unresolved references |
  | --- | --- | --- | --- |
  | `…splitter._cstage1` | unsafe definition | `…splitter`: constant with IR | none |
  | `…splitter._cstage2` | unsafe definition | `…splitter`: constant with IR | `_obj`, `_neutral`, `…splitter._rarg` (IR only) |
  | `…splitter._rarg._cstage2` | unsafe definition | `…splitter._rarg`: IR only, in `extraConstNames` | `_obj` |

- `inventory-core.json` (`--inventory Init Lean`, 145,488 entries) and
  `inventory-mathlib.json` (`--inventory Mathlib`, 461,882 entries): the only
  unresolved stage references are `_obj`, `_neutral` and `_unreachable`, all at
  stage 2. Five imported Mathlib stage-1 entries carry leaked `_kernel_fresh.N`
  free variables; they are listed in the file.

The stage entries are created by the old code generator when
`Lean.Meta.Match.mkEquationsFor` calls `addAndCompile` on the on-demand splitter
(`Lean/Meta/Match/MatchEqs.lean`). The IR side is `declMapExt` with
`Environment.addExtraName` (`Lean/Compiler/IR/CompilerM.lean`).

## Caller inventory

Every validation entry point uses the shared `runValidation`:
every new state published by `goal.start`, `frontend.process` and the other
allocating commands (`newGoalState` in `Repl.lean`), `goal.tactic` and native
operation exports through `validateOperation` (`Library.lean`: tactic, assign,
have, define, let, conv, conv exit, calc, motivated apply, no-confuse), `goal.inspect` and
`goal.continue` (`Transition.lean`, `Repl.lean`), and certification
(`Certify.lean`, which validates the snapshot and then runs its own dependency
scan). Both the shared validator and the certification scan apply the
classifier.

## Verification

Final executable sha256
`6cba4f74fdf2bc8ba7060603e7bc11feffb7229dd8c288ec7c3c0ba2e9c2ef29`.

- `lake build repl test scope_diagnostic compiler_diagnostic`
- `lake test`: 410 assertions pass (`native-tests.log`), 17 of them new in
  `CompilerValidation`.
- `lake env python3 scripts/test_scope_aware_validation.py --mathlib ~/lean-env/mathlib4 --mathlib-reference ~/lean-env/mathlib4 --capture pantograph_backport/compiler_aware_validation`:
  44 core and 40 Mathlib exchanges (`capture.json`). Mathlib is the pinned
  `29dcec074de168ac2bf835a77ef68bbe069194c5`; 4,737 source files verified.

Historical captures under `scope_aware_validation/`, `transactional_resources/`
and `live_capture/` keep their original versions and hashes.
