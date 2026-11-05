# Representation-aware environment audit, validation version 3

Tactics that generate equations or match splitters compile them on demand. The
pinned code generator then stores its intermediate stages in the retained
environment as constants. Validation version 2 read every new constant with the
kernel grammar, so the first compiler sentinel ended the session:

```text
execution owner=declaration _private.0.Nat.pow.match_1.splitter._rarg._cstage2
path=environment audit/declaration-type/binder-type:
Missing proof dependency _obj
```

`unfold Nat.pow`, `simp only [Nat.pow]` and `rw [Nat.pow]` reproduce it with only
`Init` imported, in a fresh process and after earlier history
([evidence](../pantograph_backport/compiler_aware_validation/README.md)).

## Contract

`protocol.describe` reports `transitionValidationVersion: 3`. Successful tactic
responses include exactly:

```json
{"version":3,"scope":"execution-closure-and-representation-aware-audit","checked":true}
```

Protocol version 3, transition provenance, model expressions, inspection,
certification, and transactional resources keep their versions. There is no
version-2 fallback: the two versions audit different boundaries. A validation
failure is still `error: "validation"`, allocates nothing, and ends the session.
[The schema](scope_aware_validation.schema.json) and
[fixtures](scope_aware_validation.fixtures.json) are the strict contract.

## What the compiler stores

Lean 4.10's code generator registers, for a compiled declaration `owner`:

| Entry | Form | References |
| --- | --- | --- |
| `owner._cstage1` | unsafe definition, added without a kernel check | constants and IR declarations |
| `owner._cstage2` | unsafe definition, no universe parameters | also `_obj`, `_neutral`, `_unreachable` |
| `owner` IR, `owner._rarg`, `owner._boxed`, … | IR declarations in `declMapExt`; names without constants are in `extraConstNames` | — |

The sentinel set and shapes come from every imported stage entry: 145,488 with
`Init` and `Lean`, 461,882 with the pinned Mathlib. Stage-2 entries reference no
other unresolved names and stage-1 entries none at all. No entry has
metavariables or loose bound variables. Five Mathlib stage-1 entries contain
free variables named `_kernel_fresh.N`, left by the code generator; they are
imported, so the audit never reads them. A fresh entry of that form is still an
integrity failure. That is deliberate and can be revisited if a compiler-producing
tactic is found to emit one.

## Classification

The shared module `Pantograph/DeclarationAudit.lean` classifies each entry that
is not in the trusted environment:

- **Compiler representation**: a `_cstage1` or `_cstage2` name, an unsafe
  definition, no universe parameters at stage 2, a stage-1 owner that is a
  constant, and IR for the owner that the compiler registered in this
  environment but not in the trusted one.
- **Kernel declaration**: everything else, including an entry that is only
  spelled like a stage. It keeps the strict execution audit, so an unregistered
  `Fake._cstage2` that uses `_obj` still fails.

Neither the spelling, `isUnsafe`, nor membership in the newly added map segment
is a classifier on its own; the compiler's IR registration is the provenance.

## Audits by role

- A compiler representation found by the environment enumeration is audited as
  compiler data: closed, and every reference resolves to a constant, an IR
  declaration, or (stage 2) a sentinel. It does not set `hasUnsafe`: it is
  runtime machinery, not a proof hazard. This checks the stored representation;
  it does not verify generated code.
- Any expression reference to a compiler representation is rejected:
  `Compiler-only declaration … is not a proof dependency`. The check runs before
  memoization, so an entry already audited as compiler data cannot satisfy a
  later kernel reference.
- Certification's dependency scan applies the same rule, and compiler entries
  are never copied into the kernel environment that checks the root. Kernel
  auxiliaries such as the splitter itself are reconstructed and checked as
  before.

Kernel declarations, retained locals, admissions, unsafe proof dependencies, new
axioms, and the root-statement identity keep the version-2 checks. Polling,
bounded diagnostics, cycle detection, and transactional rollback are unchanged.

## Verification

- `lake test`: 410 assertions, including `CompilerValidation` (compiler
  transitions, continuation, inspection, certification, name-only and
  malformed entries, compiler references from proofs and kernel declarations,
  sentinels in kernel expressions, warmed history).
- `lake env python3 scripts/test_scope_aware_validation.py`: core and pinned
  Mathlib exchanges, including `unfold Nat.pow` → `split` → `rfl` → `rfl` with a
  kernel receipt and `cases n <;> simp [Nat.pow]` under Mathlib.
- `.lake/build/bin/compiler_diagnostic [--inventory] Init Lean`: the provenance
  table and the sentinel inventory above.
