import Pantograph

open Lean Elab Tactic

/-- Test-only operation that reaches the unsafe scanner with an elaborated assignment. -/
elab "contract_unsafe" : tactic => do
  let name := `ContractFixtures.unsafeProof
  let info : DefinitionVal := {
    name, levelParams := [], type := mkConst ``True,
    value := mkConst ``True.intro, hints := .opaque, safety := .unsafe
  }
  addDecl (.defnDecl info)
  (← getMainGoal).assign (mkConst name)
  setGoals []

/-- A new safe dependency whose value contains an admission. -/
elab "contract_dependency_sorry" : tactic => do
  let value ← Meta.mkSorry (mkConst ``True) false
  let name := `ContractFixtures.admittedProof
  let info : DefinitionVal := {
    name, levelParams := [], type := mkConst ``True,
    value, hints := .opaque, safety := .safe
  }
  addDecl (.defnDecl info)
  (← getMainGoal).assign (mkConst name)
  setGoals []

/-- Deliberately remove a reachable proof hole from the visible list. -/
elab "contract_hidden_hole" : tactic => do
  let goal ← getMainGoal
  let hole ← Meta.mkFreshExprSyntheticOpaqueMVar (← goal.getType)
  goal.assign hole
  setGoals []

/-- Mutate the environment and close the goal before reporting a logged error. -/
elab "contract_failed_mutation" : tactic => do
  let info : DefinitionVal := {
    name := `ContractFixtures.failedMutation, levelParams := [], type := mkConst ``True,
    value := mkConst ``True.intro, hints := .opaque, safety := .safe
  }
  addDecl (.defnDecl info)
  (← getMainGoal).assign (mkConst ``True.intro)
  setGoals []
  discard <| Meta.inferType (mkConst `ContractFixtures.failedMutation)
  logError "mutation must roll back"

/-- Keep a newly introduced declaration in a partial state for a later tactic. -/
elab "contract_store_admission" : tactic => do
  let value ← Meta.mkSorry (mkConst ``True) false
  addDecl (.defnDecl {
    name := `ContractFixtures.storedAdmission, levelParams := [], type := mkConst ``True,
    value, hints := .opaque, safety := .safe
  })

/-- A tagged diagnostic verifies that the wire kind comes from the message data. -/
elab "contract_tagged_warning" : tactic => do
  logWarning (.tagged `ContractFixtures.warningKind m!"tagged warning")

/-- Reuse a failed declaration's name with a different type to test cache rollback. -/
elab "contract_reuse_failed_name" : tactic => do
  let name := `ContractFixtures.failedMutation
  addDecl (.defnDecl {
    name, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 0, hints := .opaque, safety := .safe
  })
  unless (← Meta.inferType (mkConst name)).isConstOf ``Nat do
    throwError "failed declaration type cache leaked"
  (← getMainGoal).assign (mkConst name)
  setGoals []

/-- A delayed assignment whose pending proof was omitted from the goal list. -/
elab "contract_delayed_hole" : tactic => do
  let goal ← getMainGoal
  let pending ← Meta.mkFreshExprSyntheticOpaqueMVar (← goal.getType)
  assignDelayedMVar goal #[] pending.mvarId!
  setGoals []

/-- Missing assignment declarations must produce a named validation error. -/
elab "contract_missing_assignment" : tactic => do
  (← getMainGoal).assign (.mvar ⟨`ContractFixtures.missingAssignment⟩)
  setGoals []

/-- A reachable unresolved let value must survive a closed visible goal list. -/
elab "contract_hidden_local_value" : tactic => withMainContext do
  let goal ← getMainGoal
  let hole ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  Meta.withLetDecl `hiddenValue (mkConst ``True) hole fun value => do
    goal.assign (← Meta.mkLetFVars #[value] value)
  setGoals []

/-- Close the goal with an axiom added during the search. -/
elab "contract_new_axiom" : tactic => do
  let goal ← getMainGoal
  let name := `ContractFixtures.searchAxiom
  addDecl (.axiomDecl { name, levelParams := [], type := ← instantiateMVars (← goal.getType), isUnsafe := false })
  goal.assign (mkConst name)
  setGoals []

/-- Close the goal with a checked auxiliary lemma added during the search. -/
elab "contract_auxiliary_lemma" : tactic => do
  let goal ← getMainGoal
  let name := `ContractFixtures.auxiliaryLemma
  addDecl (.thmDecl { name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
  goal.assign (mkConst name)
  setGoals []

/-- Exercise Lean's native reduction heartbeat checks without completing the proof. -/
elab "contract_heartbeat" : tactic => do
  let mut expr := mkNatLit 0
  for _ in [:1000000] do
    expr := mkApp (mkConst ``Nat.succ) expr
    discard <| Meta.whnf expr

/-- Exhaust the configured recursion depth through Lean's own guard. -/
elab "contract_recursion" : tactic => do
  let rec go : Nat → Elab.Tactic.TacticM Unit
    | 0 => pure ()
    | n + 1 => withIncRecDepth (go n)
  go 100000

/-- Recurse to a given depth through Lean's own guard, then close the goal. -/
elab "contract_recursion_depth " depth:num : tactic => do
  let rec go : Nat → Elab.Tactic.TacticM Unit
    | 0 => pure ()
    | n + 1 => withIncRecDepth (go n)
  go depth.getNat
  (← getMainGoal).assign (mkConst ``True.intro)
  setGoals []

/-- Exhaust the recursion depth while elaborating a term. -/
elab "contract_recursion_term" : term => do
  let rec go : Nat → Elab.Term.TermElabM Unit
    | 0 => pure ()
    | n + 1 => withIncRecDepth (go n)
  go 100000
  return mkConst ``True.intro

/-- Change the goal state, then exhaust the recursion depth. -/
elab "contract_recursion_after_change" : tactic => do
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  setGoals []
  let rec go : Nat → Elab.Tactic.TacticM Unit
    | 0 => pure ()
    | n + 1 => withIncRecDepth (go n)
  go 100000

/-- Exercise a fatal exception at the executable transaction boundary. -/
elab "contract_internal_failure" : tactic => do
  throw <| Exception.internal Pantograph.commandResourceExceptionId

/-- An internal failure inside an inner observation phase, propagating unchanged. -/
elab "contract_inner_phase_failure" : tactic => do
  Pantograph.withCommandPhase "observe" do
    throw <| Exception.internal Pantograph.commandResourceExceptionId

/-- A handled inner failure followed by a different fatal failure during execution. -/
elab "contract_handled_then_internal" : tactic => do
  try
    Pantograph.withCommandPhase "observe" do
      throwError "handled observation failure"
  catch _ => pure ()
  throw <| Exception.internal Pantograph.commandResourceExceptionId

/-- An error whose message cannot be rendered: the tactic's own error handler fails. -/
elab "contract_unrenderable_error" : tactic => do
  throwError (MessageData.ofLazy (fun _ => throw (IO.userError "contract render failure"))
    (fun _ => false))

/-- Spend allocations while a lazy diagnostic is rendered, after tactic execution. -/
elab "contract_diagnostic_heartbeat" : tactic => do
  let data := MessageData.ofLazy (fun _ => do
    let values ← IO.mkRef (#[] : Array Nat)
    for index in [:1000000] do
      values.modify (·.push index)
    return Dynamic.mk ("rendered" : MessageData)) (fun _ => false)
  logInfo data

unsafe def ContractFixtures.unusedUnsafe : Nat := 0

/-- Elaboration residue whose owner no longer contains a discarded local. -/
elab "contract_inert_residue" : tactic => do
  let scratch ← Meta.mkFreshExprSyntheticOpaqueMVar (mkSort .zero)
  let discarded ← mkFreshFVarId
  scratch.mvarId!.assign (.fvar discarded)
  (← getMainGoal).assign (mkConst ``True.intro)
  setGoals []

/-- An integrity failure after a native command-visible environment mutation. -/
elab "contract_invalid_mutation" : tactic => do
  let name := `ContractFixtures.invalidMutation
  addDecl (.defnDecl {
    name, levelParams := [], type := mkConst ``True,
    value := mkConst ``True.intro, hints := .opaque, safety := .safe })
  (← getMainGoal).assign (.fvar (← mkFreshFVarId))
  setGoals []
