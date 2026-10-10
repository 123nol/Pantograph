import Pantograph.Goal

namespace Pantograph
open Lean

/-- Evidence produced by inspecting one transition's elaborated expressions. -/
structure CheckedTransition where
  state : GoalState
  hasSorry : Bool
  hasUnsafe : Bool

private structure Scan where
  mvars : Lean.HashSet (MVarId × Bool) := {}
  fvars : Lean.HashSet (FVarId × Bool) := {}
  constants : Lean.HashSet (Name × Bool) := {}
  activeMVars : Lean.HashSet MVarId := {}
  unresolved : Array MVarId := #[]
  hasSorry : Bool := false
  hasUnsafe : Bool := false

private abbrev ScanM := StateT Scan (Except String)

mutual
  private partial def inspectExpr (before : Environment) (after : Environment)
      (mctx : MetavarContext) (track : Bool) (lctx : LocalContext) (expr : Expr) : ScanM Unit := do
    if expr.hasSorry then modify fun s => { s with hasSorry := true }
    match expr with
    | .mvar id => inspectMVar before after mctx track id
    | .fvar id =>
      unless (← get).fvars.contains (id, track) do
        modify fun s => { s with fvars := s.fvars.insert (id, track) }
        let some decl := lctx.find? id | throw s!"Missing local declaration {id.name}"
        inspectExpr before after mctx track lctx decl.type
        if let some value := decl.value? then inspectExpr before after mctx track lctx value
    | .const name _ =>
      unless (← get).constants.contains (name, track) do
        modify fun s => { s with constants := s.constants.insert (name, track) }
        let some info := after.find? name | throw s!"Missing proof dependency {name}"
        if info.isUnsafe then modify fun s => { s with hasUnsafe := true }
        -- Imported declarations remain the fixed trust basis.
        unless (before.find? name).isSome do
          inspectExpr before after mctx track {} info.type
          if let some value := info.value? then inspectExpr before after mctx track {} value
    | .app fn arg =>
      inspectExpr before after mctx track lctx fn
      inspectExpr before after mctx track lctx arg
    | .lam _ type body _ | .forallE _ type body _ =>
      inspectExpr before after mctx track lctx type
      inspectExpr before after mctx track lctx body
    | .letE _ type value body _ =>
      inspectExpr before after mctx track lctx type
      inspectExpr before after mctx track lctx value
      inspectExpr before after mctx track lctx body
    | .mdata _ body => inspectExpr before after mctx track lctx body
    | .proj name index body =>
      let some field := (getStructureFields after name).get? index | throw s!"Missing projection field {name}.{index}"
      let some projector := getProjFnForField? after name field | throw s!"Missing projection dependency {name}.{field}"
      inspectExpr before after mctx track lctx (.const projector [])
      inspectExpr before after mctx track lctx body
    | _ => pure ()

  private partial def inspectContext (before : Environment) (after : Environment)
      (mctx : MetavarContext) (track : Bool) (decl : MetavarDecl) : ScanM Unit := do
    inspectExpr before after mctx track decl.lctx decl.type
    for localDecl in decl.lctx do
      inspectExpr before after mctx track decl.lctx (.fvar localDecl.fvarId)

  private partial def inspectMVar (before : Environment) (after : Environment)
      (mctx : MetavarContext) (track : Bool) (id : MVarId) : ScanM Unit := do
    if (← get).activeMVars.contains id then throw s!"Cyclic metavariable assignment {id.name}"
    unless (← get).mvars.contains (id, track) do
      modify fun s => { s with mvars := s.mvars.insert (id, track) }
      let some decl := mctx.findDecl? id | throw s!"Missing metavariable declaration {id.name}"
      inspectContext before after mctx (track && !mctx.eAssignment.contains id && !mctx.dAssignment.contains id) decl
      if let some value := mctx.eAssignment.find? id then
        modify fun s => { s with activeMVars := s.activeMVars.insert id }
        inspectExpr before after mctx track decl.lctx value
        modify fun s => { s with activeMVars := s.activeMVars.erase id }
      else if let some delayed := mctx.dAssignment.find? id then
        let some pending := mctx.findDecl? delayed.mvarIdPending | throw "Missing delayed assignment target"
        for value in delayed.fvars do inspectExpr before after mctx track pending.lctx value
        modify fun s => { s with activeMVars := s.activeMVars.insert id }
        inspectMVar before after mctx track delayed.mvarIdPending
        modify fun s => { s with activeMVars := s.activeMVars.erase id }
      else if track then
        modify fun s => { s with unresolved := s.unresolved.push id }
end

/-- Inspect changed assignments, reachable dependencies and new local contexts.
    Unresolved reachable holes become goals; existing dormant siblings keep their mode semantics. -/
def validateTransition (before after : GoalState) (selected : MVarId) : Except String CheckedTransition := do
  let action : ScanM Unit := do
    inspectMVar before.trustedEnv after.env after.mctx true selected
    for goal in before.goals do inspectMVar before.trustedEnv after.env after.mctx true goal
    for goal in after.goals do inspectMVar before.trustedEnv after.env after.mctx true goal
    let changed := after.mctx.eAssignment.foldl (init := #[]) fun acc id value =>
      if (before.mctx.eAssignment.find? id).any (Expr.equal value) then acc else acc.push id
    for id in changed do inspectMVar before.trustedEnv after.env after.mctx false id
    let delayed := after.mctx.dAssignment.foldl (init := #[]) fun acc id value =>
      match before.mctx.dAssignment.find? id with
      | some old => if old.mvarIdPending == value.mvarIdPending && old.fvars == value.fvars then acc else acc.push id
      | none => acc.push id
    for id in delayed do inspectMVar before.trustedEnv after.env after.mctx false id
    -- New contexts can contain admissions in let values even if the final proof ignores them.
    let contexts := after.mctx.decls.foldl (init := #[]) fun acc id decl =>
      if before.mctx.decls.contains id then acc else acc.push decl
    for decl in contexts do inspectContext before.trustedEnv after.env after.mctx false decl
    for id in after.savedState.term.elab.pendingMVars do
      inspectMVar before.trustedEnv after.env after.mctx false id
  let (_, evidence) ← action.run {}
  let dormant := before.goals.filter (· != selected)
  let conversion := after.convMVar?.map (fun (rhs, goal, siblings) => rhs :: goal :: siblings) |>.getD []
  -- A retained conversion equation owns its evolving right-hand expression.
  let conversion := after.goals.foldl (init := conversion) fun acc goal =>
    match after.mctx.findDecl? goal with
    | some decl =>
      if (isLHSGoal? decl.type).isSome then
        let (rhs, _) := instantiateMVarsCore after.mctx decl.type.consumeMData.appArg!
        acc ++ (rhs.collectMVars {}).result.toList
      else acc
    | none => acc
  let extra := evidence.unresolved.toList.filter fun id =>
    !after.goals.contains id && !dormant.contains id && !conversion.contains id
  let state := { after with savedState := {
    after.savedState with tactic := { goals := after.goals ++ extra }
  } }
  return { state, hasSorry := evidence.hasSorry, hasUnsafe := evidence.hasUnsafe }

end Pantograph
