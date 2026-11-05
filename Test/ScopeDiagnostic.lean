import Pantograph

open Lean Pantograph

/-- This baseline walk is diagnostic evidence, not the production ownership inventory. -/
private partial def reachable (state : GoalState) (id : MVarId) : StateM (HashSet MVarId) Unit := do
  if (← get).contains id then return
  modify (·.insert id)
  let scan (e : Expr) := (e.collectMVars {}).result.forM (reachable state)
  if let some decl := state.mctx.findDecl? id then
    scan decl.type
    for localDecl in decl.lctx do
      scan localDecl.type
      if let some value := localDecl.value? then scan value
  if let some value := state.mctx.eAssignment.find? id then scan value
  if let some delayed := state.mctx.dAssignment.find? id then
    delayed.fvars.forM scan
    reachable state delayed.mvarIdPending

private def diagnostic : CoreM Json := do
  let .ok root ← goalStartExpr "∀ (p q : Prop), p ∧ q → q ∧ p" #[] | throwError "start failed"
  let .success before ← runTermElabM (root.tryTactic root.root "intro p q") | throwError "intro failed"
  let selected := before.goals.head!
  let .success after ← runTermElabM (before.tryTactic selected "tauto") | throwError "tauto failed"
  let closure := ((reachable after after.root).run {}).2
  let mut residue := #[]
  for (id, value) in after.mctx.eAssignment.toList do
    if (before.mctx.eAssignment.find? id).any (Expr.equal value) then continue
    let some decl := after.mctx.findDecl? id | continue
    let missing := (Lean.collectFVars {} value).fvarIds.filter fun fvar => !(decl.lctx.find? fvar).isSome
    unless missing.isEmpty do
      residue := residue.push <| Json.mkObj [
        ("owner", toJson id.name.toString), ("assignmentKind", "ordinary"),
        ("type", toJson (toString decl.type)), ("rootReachable", toJson (closure.contains id)),
        ("missingInOwner", toJson (missing.map (·.name.toString))),
        ("value", toJson ((toString value).take 512))]
  let checked ← validateTransition before after selected
  let certificate ← certifyRoot after 200000
  return Json.mkObj [
    ("auxiliaryAudit", toJson (checked.toOption.map (·.auxiliaryResidue) |>.getD #[])),
    ("validator", match checked with | .ok _ => "accepted" | .error message => toJson message),
    ("rootCertificate", toJson certificate), ("assignments", toJson residue),
    ("pending", toJson (after.savedState.term.elab.pendingMVars.map (·.name.toString))),
    ("synthetic", toJson (after.savedState.term.elab.syntheticMVars.toList.map (·.1.name.toString))),
    ("errorOwners", toJson (after.savedState.term.elab.mvarErrorInfos.map (·.mvarId.name.toString))),
    ("letRecCount", toJson after.savedState.term.elab.letRecsToLift.length),
    ("postponedCount", toJson after.metaState.postponed.size),
    ("zetaDeltaCount", toJson after.metaState.zetaDeltaFVarIds.size)]

unsafe def main : IO Unit := do
  Pantograph.initSearch ""
  let ctx ← createCoreContext #[]
  let state ← createCoreState #["Mathlib"]
  let (result, _) ← diagnostic.toIO ctx state
  IO.println result.compress
