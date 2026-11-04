import Test.Common
import Test.ContractFixtures
import Repl

namespace Pantograph.Test.Transaction
open Lean Pantograph.Repl

private def command (cmd : String) (fields : List (String × Json) := []) : Protocol.Command :=
  { cmd, payload := Json.mkObj fields }

private def field (response : Json) (key : String) : String :=
  response.getObjValAs? String key |>.toOption |>.getD ""

private def burn : CoreM Unit := do
  for _ in [:1000000] do
    discard <| Meta.whnf (mkApp (mkConst ``Nat.succ) (mkNatLit 0)) |>.run'

private def tests : MainM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let start ← execute (command "goal.start" [("expr", .str "True")])
  let root := start.getObjValAs? Nat "stateId" |>.toOption |>.getD 99999
  discard <| execute (command "env.add" [("name", .str "Transaction.kept"),
    ("type", .str "True"), ("value", .str "True.intro"), ("isTheorem", .bool false)])
  discard <| execute (command "goal.print" [("stateId", toJson root)])
  tests := tests ++ LSpec.test "goal printing preserves subsequent environment additions"
    ((← getEnv).contains `Transaction.kept)
  let entry ← get
  let env ← getEnv
  let coreEntry ← getThe Core.State
  let mut limits := #[]
  for phase in ["execute", "validate", "observe", "serialize"] do
    let result ← runTransaction (command "goal.start") do
      -- Stage changes to all retained allocations, options, and the environment.
      modify fun s => { s with
        nextId := 99999, goalStates := {},
        options := { s.options with printExprAST := true } }
      let added ← Pantograph.Environment.addDecl {
        name := "Transaction.staged", type := "True", value := "True.intro", isTheorem := false }
      unless added.toOption.isSome && (← getEnv).contains `Transaction.staged do
        throwError "staged declaration was not installed"
      modifyEnv fun env => env.setMainModule `MustBeDiscarded
      modifyThe Core.State fun s => { s with nextMacroScope := 99999 }
      logInfo "discarded command message"
      withCommandPhase phase do
        burn
        return Json.null
    let resource := result.response.getObjVal? "resource" |>.toOption |>.getD Json.null
    limits := limits.push (resource.getObjValAs? Nat "limit" |>.toOption |>.getD 0)
    tests := tests ++ LSpec.test s!"{phase} has a single recoverable resource envelope"
      (!result.fatal && field result.response "error" == "resource" &&
        field result.response "recovery" == "command-rolled-back" && field resource "phase" == phase &&
        (Json.parse result.bytes).toOption == some result.response && !result.bytes.contains '\n' &&
        (result.response.getObjVal? "stateId").toOption.isNone)
    tests := tests ++ LSpec.test s!"{phase} discards all staged mutations"
      ((← get).nextId == entry.nextId && (← get).goalStates.size == entry.goalStates.size &&
        !(← get).options.printExprAST && (← getEnv).mainModule == env.mainModule &&
        !(← getEnv).contains `Transaction.staged && (← getEnv).contains `Transaction.kept &&
        (← getThe Core.State).nextMacroScope == coreEntry.nextMacroScope &&
        (← getThe Core.State).messages.toArray.size == coreEntry.messages.toArray.size)
  tests := tests ++ LSpec.test "reported limits use option units" (limits.all (· == 100))
  let deletion ← runTransaction (command "goal.delete") do
    modify fun s => { s with goalStates := s.goalStates.erase root }
    withCommandPhase "serialize" do
      burn
      return Json.null
  tests := tests ++ LSpec.test "deletion remains staged until complete response encoding"
    (!deletion.fatal && (← get).goalStates.contains root)
  let rendering ← executeCommand (command "goal.tactic"
    [("stateId", toJson root), ("tactic", .str "contract_diagnostic_heartbeat")])
  let resource := rendering.response.getObjVal? "resource" |>.toOption |>.getD Json.null
  tests := tests ++ LSpec.test "lazy diagnostic exhaustion is observed without replaying messages"
    (!rendering.fatal && field resource "phase" == "observe" && (← get).goalStates.size == 1)
  let usageStart ← IO.getNumHeartbeats
  for _ in [:3000] do
    let result ← executeCommand (command "stat")
    unless !result.fatal && (result.response.getObjValAs? Nat "nGoals").toOption == some 1 do
      throwError "cheap command failed"
  let used := (← IO.getNumHeartbeats) - usageStart
  tests := tests ++ LSpec.test "combined cheap work exceeds one request budget" (used > 100000)
  let timedOut ← executeCommand (command "goal.tactic" [("stateId", toJson root), ("tactic", .str "contract_heartbeat")])
  tests := tests ++ LSpec.test "native tactic timeout reaches the shared classifier"
    (field timedOut.response "error" == "resource" && !timedOut.fatal)
  let solved ← execute (command "goal.tactic" [("stateId", toJson root), ("tactic", .str "exact True.intro")])
  let done := solved.getObjValAs? Nat "nextStateId" |>.toOption |>.getD 99999
  let certified ← execute (command "goal.certify" [("stateId", toJson done)])
  tests := tests ++ LSpec.test "the original retained state supports a certified proof after timeout"
    (field certified "status" == "certified")
  let exhausted ← runTransaction (command "goal.certify") do
    burn
    return Json.null
  tests := tests ++ LSpec.test "outer certification exhaustion is inconclusive without a receipt"
    (field exhausted.response "status" == "inconclusive" && !exhausted.fatal &&
      (exhausted.response.getObjVal? "receipt").toOption.isNone)
  let fatal ← runTransaction (command "stat") do
    throwError "unexpected failure"
  let after ← executeCommand (command "stat")
  tests := tests ++ LSpec.test "unexpected failure ends the session and rejects later dispatch"
    (fatal.fatal && after.fatal && field fatal.response "error" == "internal" &&
      field fatal.response "recovery" == "session-unusable")
  return tests

def suite (_ : Environment) : List (String × IO LSpec.TestSeq) := [
  ("Command rollback and native budgets", do
    let env ← importModules #[{ module := `Test.ContractFixtures }] {} (trustLevel := 1)
    runCoreMSeq env (tests.run { imports := ["Test.ContractFixtures"] } |>.run' {}) #["maxHeartbeats=100"])
]

end Pantograph.Test.Transaction
