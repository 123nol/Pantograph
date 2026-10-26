import Test.Common
import Test.ContractFixtures
import Repl

namespace Pantograph.Test.Snapshot
open Lean Pantograph.Repl

private def request (cmd : String) (fields : List (String × Json)) : MainM Json :=
  Repl.execute { cmd, payload := Json.mkObj fields }

private def start (expr : String) (levels : List String := []) : MainM Nat := do
  let fields := [("expr", Json.str expr)] ++
    (if levels.isEmpty then [] else [("levels", toJson levels)])
  let result ← request "goal.start" fields
  match result.getObjValAs? Nat "stateId" with
  | .ok id => pure id
  | .error _ => throwError "goal.start failed: {result}"

private def tactic (id : Nat) (text : String) (index : Nat := 0) : MainM Json :=
  request "goal.tactic" [("stateId", toJson id), ("goalId", toJson index), ("tactic", .str text)]

private def next (result : Json) : MainM Nat :=
  match result.getObjValAs? Nat "nextStateId" with
  | .ok id => pure id
  | .error _ => throwError "tactic failed: {result}"

private def names (result : Json) : Array String :=
  (result.getObjValAs? (Array Json) "goals" |>.toOption |>.getD #[]).filterMap
    fun goal => goal.getObjValAs? String "name" |>.toOption

private def field (result : Json) (key : String) : Array String :=
  (result.getObjVal? "transition").bind (·.getObjValAs? (Array String) key) |>.toOption |>.getD #[]

private def selected (result : Json) : String :=
  (result.getObjVal? "transition").bind (·.getObjValAs? String "selected") |>.toOption |>.getD ""

private def inspect (id : Nat) (goals : List String) : MainM (Array Json) := do
  let result ← request "goal.inspect" [("stateId", toJson id), ("goals", toJson goals)]
  return result.getObjValAs? (Array Json) "obligations" |>.toOption |>.getD #[]

private def status (obligation : Json) : String :=
  obligation.getObjValAs? String "status" |>.toOption |>.getD ""

private def provenanceTests : MainM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let root ← start "True ∧ True"
  let split ← tactic root "constructor"
  let pair ← next split
  tests := tests ++ LSpec.test "constructor produces two direct goals"
    (field split "direct" == names split && field split "siblings" == #[])
  let [left, right] := (names split).toList | throwError "expected two goals"
  let second ← tactic pair "trivial" 1
  tests := tests ++ LSpec.test "nonzero selection leaves its sibling, not a child"
    (selected second == right && field second "direct" == #[] && field second "siblings" == #[left])
  let first ← tactic pair "trivial" 0
  tests := tests ++ LSpec.test "either side can be solved first"
    (selected first == left && field first "siblings" == #[right])
  let unchanged ← tactic root "skip"
  tests := tests ++ LSpec.test "a goal left open is its own direct goal"
    (field unchanged "direct" == #[selected unchanged] && field unchanged "extra" == #[])
  -- The input snapshot is still usable for further alternatives.
  let again ← tactic pair "trivial" 1
  tests := tests ++ LSpec.test "input snapshot survives alternatives" (names again == #[left])

  let three ← start "True ∧ True ∧ True"
  let split ← tactic three "refine ⟨?_, ?_, ?_⟩"
  tests := tests ++ LSpec.test "identical targets stay distinct occurrences"
    ((field split "direct").size == 3 && (field split "direct").toList.eraseDups.length == 3)

  let nested ← start "∀ (p q : Prop), p → q → (p ∧ q) ∧ True"
  let opened ← tactic nested "intro p q hp hq\nconstructor"
  tests := tests ++ LSpec.test "introduced locals reported per direct goal"
    ((((opened.getObjVal? "transition").bind (·.getObjValAs? (Array (Array String)) "introduced")).toOption.map
      (·.map (·.size))) == some #[4, 4])
  let [inner, outer] := (names opened).toList | throwError "expected two goals"
  let deeper ← tactic (← next opened) "constructor"
  tests := tests ++ LSpec.test "descendants are direct and the survivor is a sibling"
    ((field deeper "direct").size == 2 && field deeper "siblings" == #[outer] &&
      !(field deeper "direct").contains inner)

  let witness ← start "∃ n : Nat, n = 0 ∧ n = 1"
  let split ← tactic witness "refine ⟨?w, ?a, ?b⟩"
  let parts ← next split
  let [w, a, b] := (names split).toList | throwError "expected three goals"
  let zero ← tactic parts "exact (rfl : 0 = 0)" 1
  tests := tests ++ LSpec.test "a shared assignment closes and changes siblings"
    (field zero "closed" == #[w] && field zero "changed" == #[b] && field zero "siblings" == #[b])
  let witnessOne ← tactic parts "exact 1" 0
  tests := tests ++ LSpec.test "assigning the witness changes both equalities"
    (field witnessOne "changed" == #[a, b])
  let pending ← inspect parts [w, a, b]
  tests := tests ++ LSpec.test "alternatives keep separate assignments"
    (pending.map status == #["active", "active", "active"])
  let afterZero ← next zero
  let rootState ← inspect afterZero [w, a, b]
  tests := tests ++ LSpec.test "solved goals absent from the list are inspectable"
    (rootState.map status == #["complete", "complete", "active"])

  let delayed ← start "True"
  let hidden ← tactic delayed "contract_delayed_hole"
  tests := tests ++ LSpec.test "restored delayed obligation is extra, not direct"
    ((field hidden "extra").size == 1 && field hidden "direct" == #[])

  let unknown ← request "goal.inspect" [("stateId", toJson parts), ("goals", toJson ["_uniq.999999"])]
  tests := tests ++ LSpec.test "unknown obligation is an index error"
    ((unknown.getObjValAs? String "error").toOption == some "index")
  let duplicate ← request "goal.inspect" [("stateId", toJson parts), ("goals", toJson [w, w])]
  tests := tests ++ LSpec.test "duplicate inspection request rejected"
    ((duplicate.getObjValAs? String "error").toOption == some "arguments")
  let still ← tactic parts "exact 0" 0
  tests := tests ++ LSpec.test "state usable after failed inspection" ((names still).size == 2)

  let ids := (← get).goalStates.toList.map (·.1)
  discard <| request "goal.delete" [("stateIds", toJson ids)]
  return tests

def suite (_env : Environment) : List (String × IO LSpec.TestSeq) := [
  ("Transition provenance and inspection", do
    let env ← importModules #[{ module := `Test.ContractFixtures }] {} (trustLevel := 1)
    runCoreMSeq env (provenanceTests.run { imports := ["Test.ContractFixtures"] } |>.run' {})),
]

end Pantograph.Test.Snapshot
