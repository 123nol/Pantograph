/-
Kernel certification of a state's complete root proof.

The proof is the instantiated root assignment, abstracted natively over the
root's local context and checked by the kernel as a theorem of the statement the
root was started with. Checking runs on a copy of the state's trusted
environment, so no search state or REPL environment sees the temporary
declaration. The kernel is always invoked directly, so `debug.skipKernelTC`
cannot turn checking off.
-/
import Pantograph.Goal

namespace Pantograph
open Lean

private structure DependencyScan where
  visited : NameSet := {}
  axioms : Array Name := #[]
  -- Declarations missing from the trusted environment, dependencies first
  auxiliary : Array Name := #[]
  problems : Array String := #[]

private abbrev ScanM := ReaderT (Environment × Environment) (StateM DependencyScan)

private def problem (message : String) : ScanM Unit :=
  modify fun s => { s with problems := s.problems.push message }

/-- Walk every constant a proof reaches, imported ones included, so that an
    admission or unsafe dependency anywhere in the closure is found. -/
private partial def scanConstant (name : Name) : ScanM Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  let (trusted, final) ← read
  let some info := final.find? name | problem s!"Missing dependency {name}"
  let isNew := !trusted.contains name
  if name == ``sorryAx then problem "Proof depends on an admission (sorryAx)"
  if info.isUnsafe then problem s!"Unsafe dependency {name}"
  let scanExpr (expr : Expr) : ScanM Unit := expr.getUsedConstants.forM scanConstant
  match info with
  | .axiomInfo _ =>
    if isNew then problem s!"New axiom {name}"
    else modify fun s => { s with axioms := s.axioms.push name }
  | .defnInfo v => scanExpr v.type; scanExpr v.value
  | .thmInfo v => scanExpr v.type; scanExpr v.value
  | .opaqueInfo v => scanExpr v.type; scanExpr v.value
  | .quotInfo _ => pure ()
  | .ctorInfo v => scanExpr v.type
  | .recInfo v => scanExpr v.type
  | .inductInfo v => scanExpr v.type; v.ctors.forM scanConstant
  if isNew then modify fun s => { s with auxiliary := s.auxiliary.push name }

private def declarationOf (info : ConstantInfo) : Except String Declaration :=
  match info with
  | .thmInfo v => if v.all.length == 1 then .ok (.thmDecl v) else .error "mutual"
  | .defnInfo v => if v.all.length == 1 then .ok (.defnDecl v) else .error "mutual"
  | .opaqueInfo v => if v.all.length == 1 then .ok (.opaqueDecl v) else .error "mutual"
  | _ => .error "unsupported kind"

private def mix (acc value : UInt64) : UInt64 :=
  (acc ^^^ value) * 1099511628211

private def levelDigest : Level → UInt64
  | .zero => 1
  | .succ l => mix 2 (levelDigest l)
  | .max a b => mix (mix 3 (levelDigest a)) (levelDigest b)
  | .imax a b => mix (mix 4 (levelDigest a)) (levelDigest b)
  | .param name => mix 5 (hash name)
  | .mvar id => mix 6 (hash id.name)

/-- A 64-bit structural digest of an expression, memoized over shared subterms.
    `Expr.hash` keeps only 32 bits, which is too few for a proof identity. Bound
    variable names are left out, so the digest identifies a term up to renaming;
    elaboration gives non-dependent arrows fresh hygienic names every time. -/
private partial def exprDigest (expr : Expr) : StateM (HashMap Expr UInt64) UInt64 := do
  if let some digest := (← get).find? expr then return digest
  let digest ← match expr with
    | .bvar index => pure (mix 11 (hash index))
    | .fvar id => pure (mix 12 (hash id.name))
    | .mvar id => pure (mix 13 (hash id.name))
    | .sort level => pure (mix 14 (levelDigest level))
    | .const name levels => pure <| levels.foldl (init := mix 15 (hash name)) fun acc l => mix acc (levelDigest l)
    | .app fn arg => return mix (mix 16 (← exprDigest fn)) (← exprDigest arg)
    | .lam _ type body info =>
      return mix (mix (mix 17 info.toUInt64) (← exprDigest type)) (← exprDigest body)
    | .forallE _ type body info =>
      return mix (mix (mix 18 info.toUInt64) (← exprDigest type)) (← exprDigest body)
    | .letE _ type value body nonDep =>
      return mix (mix (mix (mix 19 (hash nonDep)) (← exprDigest type)) (← exprDigest value)) (← exprDigest body)
    | .lit (.natVal n) => pure (mix 20 (hash n))
    | .lit (.strVal text) => pure (mix 21 (hash text))
    | .mdata _ body => return mix 22 (← exprDigest body)
    | .proj name index body => return mix (mix (mix 23 (hash name)) (hash index)) (← exprDigest body)
  modify (·.insert expr digest)
  return digest

private def digestOf (expr : Expr) : UInt64 := (exprDigest expr).run' {}

private def hex (value : UInt64) : String :=
  let digits := (Nat.toDigits 16 value.toNat).asString
  "".pushn '0' (16 - digits.length) ++ digits

/-- Identity of the trusted environment: the toolchain and the imported modules. -/
def environmentIdentity (env : Environment) : UInt64 :=
  env.header.moduleNames.foldl (init := hash Lean.githash) fun acc name => mixHash acc (hash name)

private def freshName (env : Environment) : Name := Id.run do
  let base := `_pantograph_certificate
  let mut name := base
  let mut index := 0
  while env.contains name do
    index := index + 1
    name := base.appendIndexAfter index
  return name

private def kernelOutcome (opts : Options) (error : KernelException) : CoreM (String × String) := do
  match error with
  | .deterministicTimeout => return ("inconclusive", "Kernel heartbeat budget exhausted")
  | .excessiveMemory => return ("inconclusive", "Kernel memory limit reached")
  | .deepRecursion => return ("inconclusive", "Kernel recursion limit reached")
  | .interrupted => return ("inconclusive", "Kernel check interrupted")
  | other => return ("rejected", s!"Kernel rejected the proof: {← (other.toMessageData opts).toString}")

/-- Certify the complete root proof of `state` with the kernel. Read-only. -/
def certifyRoot (state : GoalState) (maxHeartbeats : Nat) : CoreM Protocol.GoalCertifyResult := do
  let result (status reason : String) : Protocol.GoalCertifyResult :=
    { status, reason? := some reason }
  unless state.goals.isEmpty do
    return result "incomplete" s!"{state.goals.length} goals remain"
  let mctx := state.mctx
  let some rootDecl := mctx.findDecl? state.root |
    return result "rejected" "The root is not declared in this state"
  unless mctx.eAssignment.contains state.root || mctx.dAssignment.contains state.root do
    return result "incomplete" "The root is unassigned"
  let (proof, _) := instantiateMVarsCore mctx (.mvar state.root)
  if proof.hasExprMVar then
    let holes := (proof.collectMVars {}).result.toList.map (·.name.toString)
    return result "incomplete" s!"The proof has unresolved holes: {holes}"
  if proof.hasLevelMVar then
    return result "incomplete" "The proof has unresolved universe levels"
  -- Ordinary locals become binders and local definitions keep their values.
  let fvars := rootDecl.lctx.foldl (init := #[]) fun acc decl =>
    if decl.isAuxDecl then acc else acc.push (Expr.fvar decl.fvarId)
  let type := rootDecl.lctx.mkForall fvars state.rootType
  let value := rootDecl.lctx.mkLambda fvars proof
  if type.hasMVar || type.hasFVar || type.hasLooseBVars then
    return result "rejected" "The root statement is not closed"
  if value.hasFVar then
    return result "rejected" "The proof refers to a local outside the root context"
  if value.hasLooseBVars then
    return result "rejected" "The proof has loose bound variables"
  let trusted := state.trustedEnv
  let scan : ScanM Unit := do
    type.getUsedConstants.forM scanConstant
    value.getUsedConstants.forM scanConstant
  let ((), evidence) := (scan.run (trusted, state.env)).run {}
  unless evidence.problems.isEmpty do
    return result "rejected" (String.intercalate "; " evidence.problems.toList)
  let opts ← getOptions
  let budget := (maxHeartbeats * 1000).toUSize
  let mut env := trusted
  for name in evidence.auxiliary do
    let some info := state.env.find? name | return result "rejected" s!"Missing dependency {name}"
    let decl ← match declarationOf info with
      | .ok decl => pure decl
      | .error kind => return result "rejected" s!"Auxiliary declaration {name} has {kind} form"
    match Environment.addDeclCore env budget decl with
    | .ok next => env := next
    | .error error =>
      let (status, reason) ← kernelOutcome opts error
      return result status s!"{name}: {reason}"
  let name := freshName env
  let asTheorem := Declaration.thmDecl {
    name, levelParams := state.rootLevels, type, value, all := [name]
  }
  -- A root that is not a proposition is a term to construct, checked as a definition.
  let checked := match Environment.addDeclCore env budget asTheorem with
    | .error (.thmTypeIsNotProp ..) =>
      Environment.addDeclCore env budget <| .defnDecl {
        name, levelParams := state.rootLevels, type, value,
        hints := .opaque, safety := .safe, all := [name]
      }
    | other => other
  if let .error error := checked then
    let (status, reason) ← kernelOutcome opts error
    return result status reason
  return {
    status := "certified",
    receipt? := some {
      root := state.root.name.toString,
      levels := state.rootLevels.toArray.map (·.toString),
      rootType := hex (digestOf type),
      proof := hex (digestOf value),
      environment := hex (environmentIdentity trusted),
      lean := s!"{Lean.versionString} {Lean.githash}",
      axioms := (evidence.axioms.qsort (·.toString < ·.toString)).map (·.toString),
      auxiliary := evidence.auxiliary.map (·.toString),
    }
  }

end Pantograph
