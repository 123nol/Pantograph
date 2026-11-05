/-
Representation of retained environment entries.

The pinned code generator stores its intermediate stages in the environment as
ordinary constants: `owner._cstage1` (after lambda lifting) and `owner._cstage2`
(after erasure). They are unsafe definitions added without a kernel check, and
stage-2 types and values use the compiler's own sentinels (`_obj`, `_neutral`,
`_unreachable`), which are not constants. Reading them with the kernel grammar
fails on the first sentinel; exempting them by name would let any declaration
with that spelling skip the strict audit.

Classification therefore uses the compiler's registry: an entry is a compiler
representation only if the compiler registered IR for its owner in this
environment and not in the trusted one. Every other entry, including one that is
only named like a stage, is a kernel declaration and keeps the strict audit. A
compiler representation is never a proof dependency.
-/
import Lean

namespace Pantograph
open Lean

/-- How the expressions of an untrusted environment entry must be read. -/
inductive Representation where
  | kernel
  /-- Code-generator output for `owner`, at stage 1 or 2. -/
  | compiler (stage : Nat) (owner : Name)
  deriving BEq, Inhabited

/-- The constants the pinned code generator writes into stage-2 representations.
    Established from every imported stage entry of the toolchain (`Init`, `Lean`):
    no other unresolved reference occurs. -/
def compilerSentinels : List Name := [`_obj, `_neutral, `_unreachable]

private def stageOf : String → Option Nat
  | "_cstage1" => some 1
  | "_cstage2" => some 2
  | _ => none

/-- Classify an entry that is not in the trusted environment.

    Compiler representation requires all of: a stage name, an unsafe definition,
    no universe parameters at stage 2, and fresh IR registered by the compiler for
    the owner. Stage-1 owners are always constants. Anything that fails one of
    these is a kernel declaration. -/
def classifyEntry (env trusted : Environment) (name : Name) (info : ConstantInfo) : Representation :=
  match name, info with
  | .str owner suffix, .defnInfo value =>
    match stageOf suffix with
    | none => .kernel
    | some stage =>
      let freshIR := (IR.findEnvDecl env owner).isSome && (IR.findEnvDecl trusted owner).isNone
      let shaped := value.safety == .unsafe &&
        (stage == 1 && env.contains owner || stage == 2 && value.levelParams.isEmpty)
      if !trusted.contains name && freshIR && shaped then .compiler stage owner else .kernel
  | _, _ => .kernel

/-- Representation of an untrusted name, or `none` for trusted or missing names. -/
def classifyName (env trusted : Environment) (name : Name) : Option Representation :=
  if trusted.contains name then none
  else (env.find? name).map (classifyEntry env trusted name)

/-- Whether `name` is fresh compiler data, which is never a proof dependency. -/
def isCompilerRepresentation (env trusted : Environment) (name : Name) : Bool :=
  match classifyName env trusted name with
  | some (.compiler ..) => true
  | _ => false

/-- The integrity problems of a compiler representation, empty when it holds.

    The entry must be closed and every reference must resolve: to a constant, to
    a declaration the compiler registered IR for, or at stage 2 to a sentinel.
    This checks the stored representation; it does not verify generated code. -/
def compilerEntryProblems (env : Environment) (stage : Nat) (info : ConstantInfo) : Array String := Id.run do
  let mut problems := #[]
  let parts := #[("type", info.type)] ++ (info.value?.map (fun v => #[("value", v)]) |>.getD #[])
  for (part, expr) in parts do
    if expr.hasFVar then problems := problems.push s!"{part} has a free variable"
    if expr.hasMVar then problems := problems.push s!"{part} has a metavariable"
    if expr.hasLooseBVars then problems := problems.push s!"{part} has a loose bound variable"
    for used in expr.getUsedConstants do
      let resolved := env.contains used || (IR.findEnvDecl env used).isSome ||
        (stage == 2 && compilerSentinels.contains used)
      unless resolved do problems := problems.push s!"{part} has unresolved compiler reference {used}"
  return problems

end Pantograph
