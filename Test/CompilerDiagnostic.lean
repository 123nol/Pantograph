import Pantograph

open Lean Pantograph

/-! Provenance of the environment entries that compiler-producing tactics add.

This walk is diagnostic evidence for the classifier, not the production audit. -/

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

private def safetyOf : ConstantInfo → String
  | .defnInfo v => match v.safety with | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"
  | info => if info.isUnsafe then "unsafe" else "safe"

private def describe (env : Environment) (trusted : Environment) (name : Name) (info : ConstantInfo) : Json :=
  let used := info.type.getUsedConstants ++ (info.value?.map Expr.getUsedConstants |>.getD #[])
  let used := used.toList.eraseDups
  let unresolved := used.filter fun n => !env.contains n
  Json.mkObj [
    ("name", toJson name.toString), ("kind", kindOf info), ("safety", safetyOf info),
    ("levelParams", toJson (info.levelParams.map toString)),
    ("hasIR", toJson (IR.findEnvDecl env name).isSome),
    ("prefix", toJson name.getPrefix.toString),
    ("prefixHasIR", toJson (IR.findEnvDecl env name.getPrefix).isSome),
    ("prefixIsConstant", toJson (env.contains name.getPrefix)),
    ("prefixTrusted", toJson (trusted.contains name.getPrefix)),
    ("typeHasFVar", toJson info.type.hasFVar), ("typeHasMVar", toJson info.type.hasMVar),
    ("valueHasFVar", toJson (info.value?.any Expr.hasFVar)), ("valueHasMVar", toJson (info.value?.any Expr.hasMVar)),
    ("unresolved", toJson (unresolved.map toString)),
    ("unresolvedWithIR", toJson ((unresolved.filter fun n => (IR.findEnvDecl env n).isSome).map toString)),
    ("type", toJson ((toString info.type).take 300))]

private def run (expr : String) (tactics : List String) : CoreM Json := do
  let .ok root ← goalStartExpr expr #[] | throwError "start failed"
  let mut state := root
  let mut outcomes := #[]
  for tactic in tactics do
    match ← runTermElabM (state.tryTactic state.goals.head! tactic) with
    | .success next => state := next; outcomes := outcomes.push (toJson s!"{tactic}: success")
    | _ => outcomes := outcomes.push (toJson s!"{tactic}: not a success"); break
  let env := state.env
  let trusted := root.trustedEnv
  let additions := env.constants.foldStage2 (fun acc name info =>
    if trusted.contains name then acc else (name, info) :: acc) []
  let extra := env.extraConstNames.toList.filter fun n => !trusted.contains n
  let checked ← validateSnapshot state
  return Json.mkObj [
    ("goal", toJson expr), ("tactics", toJson outcomes),
    ("additions", toJson ((additions.reverse.map fun (n, i) => describe env trusted n i).toArray)),
    ("extraConstNames", toJson (extra.map toString)),
    ("extraWithIR", toJson ((extra.filter fun n => (IR.findEnvDecl env n).isSome).map toString)),
    ("validator", match checked with | .ok _ => "accepted" | .error message => toJson message)]

/-- Every imported compiler stage entry, built by the same pinned compiler: which references
    are neither constants nor IR declarations, and which shapes occur. -/
private def inventory : CoreM Json := do
  let env ← getEnv
  let mut sentinels : HashMap String Nat := {}
  let mut shapes : HashMap String Nat := {}
  let mut count := 0
  let mut withFVars : Array Json := #[]
  for (name, info) in env.constants.toList do
    let .str owner stage := name | continue
    unless stage == "_cstage1" || stage == "_cstage2" do continue
    count := count + 1
    let shape := s!"{stage} {kindOf info} {safetyOf info} ownerIR={(IR.findEnvDecl env owner).isSome} ownerConst={env.contains owner} levels={!info.levelParams.isEmpty} looseBVars={info.type.hasLooseBVars || info.value?.any Expr.hasLooseBVars} fvar={info.type.hasFVar || info.value?.any Expr.hasFVar} mvar={info.type.hasMVar || info.value?.any Expr.hasMVar}"
    shapes := shapes.insert shape (shapes.findD shape 0 + 1)
    if (info.type.hasFVar || info.value?.any Expr.hasFVar) && withFVars.size < 16 then
      let fvars := (Lean.collectFVars {} info.type).fvarIds ++ (info.value?.map (Lean.collectFVars {} · |>.fvarIds) |>.getD #[])
      withFVars := withFVars.push <| Json.mkObj [("name", toJson name.toString),
        ("module", toJson ((env.getModuleIdxFor? name).bind (env.header.moduleNames.get? ·.toNat) |>.map toString)),
        ("fvars", toJson (fvars.map (·.name.toString)))]
    let used := info.type.getUsedConstants ++ (info.value?.map Expr.getUsedConstants |>.getD #[])
    for n in used do
      unless env.contains n || (IR.findEnvDecl env n).isSome do
        let key := s!"{stage} {n}"
        sentinels := sentinels.insert key (sentinels.findD key 0 + 1)
  return Json.mkObj [("entries", toJson count), ("withFreeVariables", toJson withFVars),
    ("shapes", toJson (shapes.toList.map fun (k, v) => s!"{v} × {k}")),
    ("unresolved", toJson (sentinels.toList.map fun (k, v) => s!"{v} × {k}"))]

unsafe def main (args : List String) : IO Unit := do
  Pantograph.initSearch ""
  let ctx ← createCoreContext #[]
  let inventoryMode := args.head? == some "--inventory"
  let args := if inventoryMode then args.tail! else args
  let imports := if args.isEmpty then #["Init"] else args.toArray
  let state ← createCoreState imports
  if inventoryMode then
    let (result, _) ← inventory.toIO ctx state
    IO.println result.pretty
    return
  let cases := [
    ("∀ m n : Nat, Nat.pow m (n+1) = Nat.pow m n * m", ["intro m n", "unfold Nat.pow"]),
    ("∀ l : List Nat, List.length (0 :: l) = l.length + 1", ["intro l", "simp only [List.length]"]),
    ("∀ n : Nat, Nat.pred (n+1) = n", ["intro n", "unfold Nat.pred"])]
  for (expr, tactics) in cases do
    let (result, _) ← (run expr tactics).toIO ctx state
    IO.println result.pretty
