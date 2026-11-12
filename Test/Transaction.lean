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

private def recurse : CoreM Unit := do
  let rec go : Nat → CoreM Unit
    | 0 => pure ()
    | n + 1 => withIncRecDepth (go n)
  go 100000

/-- Exhaust one resource kind: heartbeats or recursion depth. -/
private def exhaust (kind : String) : CoreM Unit :=
  if kind == "heartbeats" then burn else recurse

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
  let mut limits : Array (String × Nat) := #[]
  for kind in ["heartbeats", "recursion-depth"] do
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
          exhaust kind
          return Json.null
      let resource := result.response.getObjVal? "resource" |>.toOption |>.getD Json.null
      limits := limits.push (kind, resource.getObjValAs? Nat "limit" |>.toOption |>.getD 0)
      tests := tests ++ LSpec.test s!"{kind} in {phase} has a single recoverable resource envelope"
        (!result.fatal && field result.response "error" == "resource" &&
          field result.response "recovery" == "command-rolled-back" && field resource "phase" == phase &&
          field resource "kind" == kind && (resource.getObjValAs? Nat "version").toOption == some 2 &&
          (Json.parse result.bytes).toOption == some result.response && !result.bytes.contains '\n' &&
          (result.response.getObjVal? "stateId").toOption.isNone)
      tests := tests ++ LSpec.test s!"{kind} in {phase} discards all staged mutations"
        ((← get).nextId == entry.nextId && (← get).goalStates.size == entry.goalStates.size &&
          !(← get).options.printExprAST && (← getEnv).mainModule == env.mainModule &&
          !(← getEnv).contains `Transaction.staged && (← getEnv).contains `Transaction.kept &&
          (← getThe Core.State).nextMacroScope == coreEntry.nextMacroScope &&
          (← getThe Core.State).messages.toArray.size == coreEntry.messages.toArray.size)
  tests := tests ++ LSpec.test "reported limits use each kind's units"
    (limits.all fun (kind, limit) => limit == if kind == "heartbeats" then 100 else 200)
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
  for kind in ["heartbeats", "recursion-depth"] do
    let exhausted ← runTransaction (command "goal.certify") do
      exhaust kind
      return Json.null
    tests := tests ++ LSpec.test s!"outer certification {kind} exhaustion is inconclusive without a receipt"
      (field exhausted.response "status" == "inconclusive" && !exhausted.fatal &&
        (exhausted.response.getObjVal? "receipt").toOption.isNone &&
        (field exhausted.response "reason").length > 0)
  -- Recursion depth: a real tactic, a native fixture and a state change before exhaustion.
  let counted ← execute (command "goal.start" [("expr", .str "(List.replicate 2000 0).length = 2000")])
  let counting := counted.getObjValAs? Nat "stateId" |>.toOption |>.getD 99999
  let before ← get
  let real ← executeCommand (command "goal.tactic"
    [("stateId", toJson counting), ("tactic", .str "decide")])
  let realResource := real.response.getObjVal? "resource" |>.toOption |>.getD Json.null
  tests := tests ++ LSpec.test "a real tactic exhausting the recursion depth is a rolled-back resource"
    (!real.fatal && field real.response "error" == "resource" &&
      field realResource "kind" == "recursion-depth" && field realResource "phase" == "execute" &&
      (realResource.getObjValAs? Nat "limit").toOption == some 200 &&
      field real.response "recovery" == "command-rolled-back" &&
      (← get).nextId == before.nextId && (← get).goalStates.size == before.goalStates.size)
  let other ← execute (command "goal.tactic" [("stateId", toJson counting), ("tactic", .str "exact List.length_replicate 2000 0")])
  let otherDone := other.getObjValAs? Nat "nextStateId" |>.toOption |>.getD 99999
  let otherCertified ← execute (command "goal.certify" [("stateId", toJson otherDone)])
  tests := tests ++ LSpec.test "another tactic on the retained input certifies in the same session"
    (field otherCertified "status" == "certified")
  let fresh ← execute (command "goal.start" [("expr", .str "True")])
  let input := fresh.getObjValAs? Nat "stateId" |>.toOption |>.getD 99999
  let entryStates := (← get).goalStates.size
  let entryNext := (← get).nextId
  let mut repeated := true
  for tactic in ["contract_recursion", "contract_recursion_after_change"] do
    for _ in [:25] do
      let result ← executeCommand (command "goal.tactic" [("stateId", toJson input), ("tactic", .str tactic)])
      let resource := result.response.getObjVal? "resource" |>.toOption |>.getD Json.null
      repeated := repeated && !result.fatal && field resource "kind" == "recursion-depth" &&
        (result.response.getObjVal? "nextStateId").toOption.isNone
  tests := tests ++ LSpec.test "repeated recursion exhaustion leaks no allocations"
    (repeated && (← get).goalStates.size == entryStates && (← get).nextId == entryNext)
  -- A scoped limit is reported as the innermost `set_option maxRecDepth` scope applied it.
  let scopedCases : List (String × Nat) := [
    ("set_option maxRecDepth 30 in contract_recursion", 30),
    ("set_option maxRecDepth 100 in contract_recursion", 100),
    ("set_option maxRecDepth 1000 in contract_recursion", 1000),
    ("set_option maxRecDepth 30 in (set_option maxRecDepth 100 in contract_recursion)", 100),
    ("set_option pp.all true in contract_recursion", 200),
    ("exact (set_option maxRecDepth 50 in contract_recursion_term)", 50),
    -- A `by` block is elaborated after the term scope has exited, under the outer limit.
    ("exact (set_option maxRecDepth 50 in (by contract_recursion))", 200)]
  for (tactic, expected) in scopedCases do
    let statesBefore := (← get).goalStates.size
    let nextBefore := (← get).nextId
    let result ← executeCommand (command "goal.tactic" [("stateId", toJson input), ("tactic", .str tactic)])
    let resource := result.response.getObjVal? "resource" |>.toOption |>.getD Json.null
    tests := tests ++ LSpec.test s!"{tactic} reports limit {expected} and rolls back"
      (!result.fatal && field resource "kind" == "recursion-depth" &&
        (resource.getObjValAs? Nat "limit").toOption == some expected &&
        field result.response "recovery" == "command-rolled-back" &&
        (← get).goalStates.size == statesBefore && (← get).nextId == nextBefore)
  let deep ← execute (command "goal.tactic"
    [("stateId", toJson input), ("tactic", .str "exact (set_option maxRecDepth 50 in (by contract_recursion_depth 120))")])
  tests := tests ++ LSpec.test "a postponed by block runs under the outer limit"
    ((deep.getObjValAs? Nat "nextStateId").toOption.isSome)
  let ordinary ← execute (command "goal.tactic"
    [("stateId", toJson input), ("tactic", .str "set_option maxRecDepth 30 in fail \"ordinary\"")])
  let ordinaryErrors := ordinary.getObjValAs? (Array String) "tacticErrors" |>.toOption |>.getD #[]
  tests := tests ++ LSpec.test "an ordinary failure inside a scope is one ordinary rejection"
    (ordinaryErrors.size == 1 && (ordinaryErrors.getD 0 "").startsWith "ordinary")
  let proof ← execute (command "goal.tactic" [("stateId", toJson input), ("tactic", .str "exact True.intro")])
  let proven := proof.getObjValAs? Nat "nextStateId" |>.toOption |>.getD 99999
  let receipt ← execute (command "goal.certify" [("stateId", toJson proven)])
  tests := tests ++ LSpec.test "a state changed before exhaustion is restored and still certifies"
    (field receipt "status" == "certified")
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
    runCoreMSeq env (tests.run { imports := ["Test.ContractFixtures"] } |>.run' {})
      #["maxHeartbeats=100", "maxRecDepth=200"])
]

end Pantograph.Test.Transaction
