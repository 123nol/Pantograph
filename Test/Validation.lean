import Test.Common
import Test.ContractFixtures
import Pantograph.Validation
import Repl

namespace Pantograph.Test.Validation
open Lean Pantograph.Repl

private def request (cmd : String) (fields : List (String × Json)) : MainM Json :=
  Repl.execute { cmd, payload := Json.mkObj fields }

private def start (expr : String) : MainM Nat := do
  let result ← request "goal.start" [("expr", .str expr)]
  match result.getObjValAs? Nat "stateId" with
  | .ok id => pure id
  | .error _ => throwError "goal.start failed: {result}"

private def tactic (id : Nat) (text : String) (index : Nat := 0) : MainM Json :=
  request "goal.tactic" [("stateId", toJson id), ("goalId", toJson index), ("tactic", .str text)]

private def success (result : Json) : Bool :=
  (result.getObjValAs? Nat "nextStateId").isOk &&
  ((result.getObjVal? "validation").bind (·.getObjValAs? Bool "checked")).toOption == some true

private def rejection (result : Json) : Bool :=
  (result.getObjValAs? (Array String) "tacticErrors").isOk &&
  !(result.getObjVal? "nextStateId").isOk &&
  (result.getObjValAs? Bool "hasSorry").toOption == some false &&
  (result.getObjValAs? Bool "hasUnsafe").toOption == some false

private def goals (result : Json) : Array Json :=
  result.getObjValAs? (Array Json) "goals" |>.toOption |>.getD #[]

private def protocolTests : MainM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let descriptor ← request "protocol.describe" []
  tests := tests ++ LSpec.test "exact descriptor" (descriptor == toJson ({} : Protocol.ProtocolDescriptor))
  let failedStart ← request "goal.start" [("expr", .str "(by run_tac Lean.logError \"start failure\"; exact True)")]
  tests := tests ++ LSpec.test "logged start errors reject state allocation" ((failedStart.getObjValAs? String "error").toOption == some "elab")
  tests := tests ++ LSpec.test "failed start allocated no state" ((← get).goalStates.isEmpty)
  let root ← start "True"
  let valid ← tactic root "trivial"
  tests := tests ++ LSpec.test "valid completed transition" (success valid && (goals valid).isEmpty)
  let skipped ← tactic root "skip"
  tests := tests ++ LSpec.test "skip preserves the open goal" (success skipped && (goals skipped).size == 1)
  let multiline ← start "∀ (p : Prop), p → p"
  let result ← tactic multiline "intro p h\nexact h"
  tests := tests ++ LSpec.test "complete multiline tactic sequence" (success result && (goals result).isEmpty)
  let bad ← tactic root "trivial\nthis_is_not_a_tactic"
  tests := tests ++ LSpec.test "trailing input rejected" ((bad.getObjValAs? String "parseError").isOk)
  let bad ← tactic root "exact Nat.zero"
  tests := tests ++ LSpec.test "ordinary type failure" (rejection bad)
  let bad ← tactic root "run_tac Lean.logError \"capture error\" <;> trivial"
  tests := tests ++ LSpec.test "logged error rejects completed tactic" (rejection bad)
  let messages := bad.getObjValAs? (Array Protocol.Message) "messages" |>.toOption |>.getD #[]
  tests := tests ++ LSpec.test "real error has source position" (messages.any fun m => m.pos.line == 1 && m.data == "capture error")
  let bad ← tactic root "contract_failed_mutation"
  tests := tests ++ LSpec.test "failed mutation rejected" (rejection bad)
  let inspected ← request "env.inspect" [("name", .str "ContractFixtures.failedMutation")]
  tests := tests ++ LSpec.test "failed environment mutation rolled back" ((inspected.getObjVal? "error").isOk)
  let natRoot ← start "Nat"
  discard <| tactic natRoot "contract_failed_mutation"
  let reused ← tactic natRoot "contract_reuse_failed_name"
  tests := tests ++ LSpec.test "failed declaration cache rolled back" (success reused && (goals reused).isEmpty)
  let result ← tactic root "trivial"
  tests := tests ++ LSpec.test "original state reusable after failures" (success result && (goals result).isEmpty)
  let result ← tactic root "run_tac Lean.logWarning \"warning evidence\"\nrun_tac Lean.logInfo \"information evidence\"\ntrivial"
  let messages := result.getObjValAs? (Array Protocol.Message) "messages" |>.toOption |>.getD #[]
  tests := tests ++ LSpec.test "warning/information survive success" (success result &&
    messages.any (fun m => m.severity == "warning" && m.data == "warning evidence") &&
    messages.any (fun m => m.severity == "information" && m.data == "information evidence"))
  let result ← tactic root "trivial"
  tests := tests ++ LSpec.test "messages do not leak to following request" ((result.getObjValAs? (Array Protocol.Message) "messages").toOption == some #[])
  for text in ["sorry", "exact (by sorry)", "have h : True := by sorry\nexact h", "contract_dependency_sorry"] do
    let result ← tactic root text
    tests := tests ++ LSpec.test s!"admission detected: {text}" (success result && (result.getObjValAs? Bool "hasSorry").toOption == some true)
  let result ← tactic root "contract_unsafe"
  tests := tests ++ LSpec.test "positive unsafe scanner evidence" (success result && (result.getObjValAs? Bool "hasUnsafe").toOption == some true)
  let stored ← tactic root "contract_store_admission"
  let storedId := stored.getObjValAs? Nat "nextStateId" |>.toOption |>.getD root
  let used ← tactic storedId "exact ContractFixtures.storedAdmission"
  tests := tests ++ LSpec.test "introduced declarations retain original trust boundary" (success used &&
    (used.getObjValAs? Bool "hasSorry").toOption == some true)
  let inspected ← request "env.inspect" [("name", .str "ContractFixtures.storedAdmission")]
  tests := tests ++ LSpec.test "serialization does not leak successful environment mutations" ((inspected.getObjVal? "error").isOk)
  let tagged ← tactic root "contract_tagged_warning"
  let messages := tagged.getObjValAs? (Array Protocol.Message) "messages" |>.toOption |>.getD #[]
  tests := tests ++ LSpec.test "message kind preserved" (messages.any fun m => m.kind == "ContractFixtures.warningKind")
  let result ← tactic root "contract_hidden_hole"
  tests := tests ++ LSpec.test "hidden reachable hole becomes a goal" (success result && (goals result).size == 1)
  let id := result.getObjValAs? Nat "nextStateId" |>.toOption |>.getD root
  let closed ← tactic id "trivial"
  tests := tests ++ LSpec.test "restored hidden hole can be solved" (success closed && (goals closed).isEmpty)
  let localHole ← tactic root "contract_hidden_local_value"
  tests := tests ++ LSpec.test "hidden local value remains an obligation" (success localHole && (goals localHole).size == 1)
  let delayed ← tactic root "contract_delayed_hole"
  tests := tests ++ LSpec.test "delayed hole restored through the protocol" (success delayed && (goals delayed).size == 1)
  let missing ← tactic root "contract_missing_assignment"
  tests := tests ++ LSpec.test "missing assignment returns named validation error" ((missing.getObjValAs? String "error").toOption == some "validation" && !(missing.getObjVal? "nextStateId").isOk)
  let conjunction ← start "True ∧ True"
  let split ← tactic conjunction "constructor"
  let id := split.getObjValAs? Nat "nextStateId" |>.toOption |>.getD conjunction
  let second ← tactic id "trivial" 1
  tests := tests ++ LSpec.test "nonzero selection preserves sibling" (success second && (goals second).size == 1)
  let ids := (← get).goalStates.toList.map (·.1)
  discard <| request "goal.delete" [("stateIds", toJson ids)]
  let count ← request "stat" []
  tests := tests ++ LSpec.test "all test allocations deleted" ((count.getObjValAs? Nat "nGoals").toOption == some 0)
  return tests

private def boundaryTests : Elab.TermElabM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let state ← GoalState.create (mkConst ``True)
  let sibling ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let state ← GoalState.createFromMVars [state.root, sibling.mvarId!] state.root
  let .success next ← state.tryTacticM state.root (do
      let value ← Meta.mkSorry (mkConst ``True) false
      sibling.mvarId!.assign value
      Elab.Tactic.setGoals [state.root]) | throwError "coupled tactic failed"
  let checked := validateTransition state next state.root
  tests := tests ++ LSpec.test "changed coupled assignment scanned" (checked.toOption.any (·.hasSorry))
  let state ← GoalState.create (mkConst ``True)
  let .success next ← state.tryTacticM state.root (do
      let pending ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
      assignDelayedMVar state.root #[] pending.mvarId!
      Elab.Tactic.setGoals []) | throwError "delayed tactic failed"
  let checked := validateTransition state next state.root
  tests := tests ++ LSpec.test "delayed pending obligation retained" (checked.toOption.any fun result => result.state.goals.length == 1)
  let missing : MVarId := ⟨`ContractFixtures.missing⟩
  let corrupted := { state with savedState := { state.savedState with tactic := { goals := [missing] } } }
  tests := tests ++ LSpec.test "missing evidence produces validation failure" (!(validateTransition state corrupted state.root).isOk)
  let cyclic := { state with savedState := { state.savedState with term := {
    state.savedState.term with meta := { state.savedState.term.meta with meta := {
      state.metaState with mctx := { state.mctx with eAssignment := state.mctx.eAssignment.insert state.root (.mvar state.root) }
    } }
  } } }
  tests := tests ++ LSpec.test "cyclic assignments reject indeterminate evidence" (!(validateTransition state cyclic state.root).isOk)
  logInfo "outer log"
  let outer := (← getThe Core.State).messages
  let .failure _ _ ← state.tryTacticM state.root (do
      (← Elab.Tactic.getMainGoal).assign (mkConst ``True.intro)
      logError "inner failure") | throwError "shared operation accepted logged error"
  let current := (← getThe Core.State).messages
  tests := tests ++ LSpec.test "outer message log restored" (current.toArray.size == outer.toArray.size)
  tests := tests ++ LSpec.test "failed assignment restored" (!(← getMCtx).eAssignment.contains state.root)
  return tests

def suite (env : Environment) : List (String × IO LSpec.TestSeq) := [
  ("Transition boundary", runTermElabMSeq env boundaryTests),
  ("Protocol diagnostics and checks", do
    let env ← importModules #[{ module := `Test.ContractFixtures }] {} (trustLevel := 1)
    runCoreMSeq env (protocolTests.run { imports := ["Test.ContractFixtures"] } |>.run' {}))
]

end Pantograph.Test.Validation
