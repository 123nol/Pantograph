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
