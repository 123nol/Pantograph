/-
Transition provenance and read-only obligation inspection for retained states.

A search keeps result states alive and runs later tactics on them directly, so
it needs to know which listed goals a tactic produced for the selected goal and
which were siblings carried over by automatic resumption. That is decided here
from metavariable identities, never from printed goals.
-/
import Pantograph.Goal
import Pantograph.Serial

namespace Pantograph
open Lean

private def isUnassigned (mctx : MetavarContext) (goal : MVarId) : Bool :=
  !(mctx.eAssignment.contains goal || mctx.dAssignment.contains goal)

private def instantiated (mctx : MetavarContext) (expr : Expr) : Expr :=
  (instantiateMVarsCore mctx expr).1

/-- Whether a goal's instantiated target or any local type or value differs
    between two snapshots of the same lineage. -/
private def goalChanged (before after : MetavarContext) (goal : MVarId) : Bool :=
  match before.findDecl? goal, after.findDecl? goal with
  | some old, some new =>
    instantiated before old.type != instantiated after new.type ||
    new.lctx.foldl (init := false) fun acc decl =>
      acc || match old.lctx.find? decl.fvarId with
        | none => true
        | some prior =>
          instantiated before prior.type != instantiated after decl.type ||
          (prior.value?.map (instantiated before)) != (decl.value?.map (instantiated after))
  | _, _ => true

/-- Locals of `child` that `parent` does not have, in context order, with the
    same visibility filter as goal serialization. -/
private def introducedLocals (options : Protocol.Options) (mctx : MetavarContext)
    (parent child : MVarId) : Array String :=
  match mctx.findDecl? child with
  | none => #[]
  | some decl =>
    let known := (mctx.findDecl? parent).map (·.lctx)
    decl.lctx.foldl (init := #[]) fun acc localDecl =>
      let hidden := !options.printAuxDecls && localDecl.isAuxDecl ||
        !options.printImplementationDetailHyps && localDecl.isImplementationDetail
      if hidden || (known.bind (·.find? localDecl.fvarId)).isSome then acc
      else acc.push localDecl.fvarId.name.toString

/-- Relate the listed goals of `after` to `before`.

`produced` is the goal list the operation itself returned for `selected`,
before automatic resumption appended the input's siblings. -/
def transitionProvenance (options : Protocol.Options) (before after : GoalState)
    (selected : MVarId) (produced : List MVarId) : Protocol.TransitionProvenance :=
  let mctx := after.mctx
  let goals := after.goals
  let prior := before.goals.filter (· != selected)
  -- A produced goal that was already an input goal stays a sibling. A selected
  -- goal the operation left open (as `skip` does) is its own direct goal.
  let direct := (produced.filter fun goal =>
    goals.contains goal && !prior.contains goal).eraseDups
  let siblings := prior.filter fun goal => goals.contains goal
  let extra := goals.filter fun goal => !direct.contains goal && !siblings.contains goal
  let name (goal : MVarId) := goal.name.toString
  {
    selected := name selected,
    direct := direct.toArray.map name,
    introduced := direct.toArray.map (introducedLocals options mctx selected),
    siblings := siblings.toArray.map name,
    changed := (siblings.filter (goalChanged before.mctx mctx)).toArray.map name,
    closed := (prior.filter fun goal => !isUnassigned mctx goal).toArray.map name,
    dormant := (prior.filter fun goal => isUnassigned mctx goal && !goals.contains goal).toArray.map name,
    extra := extra.toArray.map name,
  }

/-- Status of one obligation of a retained state. `none` if it is not declared. -/
def inspectObligation (state : GoalState) (goal : MVarId) (options : Protocol.Options) :
    MetaM (Option Protocol.ObligationInspection) := do
  let mctx := state.mctx
  let some decl := mctx.findDecl? goal | return none
  let holes (expr : Expr) : Array String :=
    (expr.collectMVars {}).result.map (·.name.toString)
  let name := goal.name.toString
  if isUnassigned mctx goal then
    let status := if state.goals.contains goal then "active" else "pending"
    let serialized ← state.withMetaState <|
      serializeGoal options goal decl (goalState? := .some state)
    let type := instantiated mctx decl.type
    let context := decl.lctx.foldl (init := #[]) fun acc localDecl =>
      let acc := acc ++ holes (instantiated mctx localDecl.type)
      match localDecl.value? with
      | some value => acc ++ holes (instantiated mctx value)
      | none => acc
    return some {
      name, status, goal? := some serialized,
      holes := (holes type ++ context).toList.eraseDups.toArray,
      universeHoles := type.hasLevelMVar,
    }
  -- A delayed assignment is complete when its pending proof is.
  let value := match mctx.dAssignment.find? goal with
    | some delayed => instantiated mctx (.mvar delayed.mvarIdPending)
    | none => instantiated mctx (.mvar goal)
  let remaining := holes value
  let complete := remaining.isEmpty && !value.hasLevelMVar
  let status :=
    if complete then "complete"
    else if mctx.eAssignment.contains goal then "assigned"
    else "delayed"
  return some { name, status, holes := remaining, universeHoles := value.hasLevelMVar }

end Pantograph
