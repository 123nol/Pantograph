import Test.Common
import Pantograph.Validation
import Pantograph.Certify
import Repl

/-! Elaboration aborts are ordinary tactic failures; unexpected failures keep evidence.

`exact`, `refine` and `have` log "don't know how to synthesize placeholder" and then
throw Lean's internal abort exception. The REPL used to treat every internal
exception as an unexpected failure and end the session. -/

namespace Pantograph.Test.FailureBoundary
open Lean

private def failsWith (fragment : String) : TacticResult → Bool
  | .failure errors _ => errors.any fun e => (e.splitOn fragment).length > 1
  | _ => false

private def placeholderTactics : List String := [
  "exact (fun (x : Nat) => True.intro) _",
  "refine (fun (x : Nat) => True.intro) _",
  "have h := (fun (x : Nat) => x) _",
  "exact (_ : True)"]

private def abortTests : Elab.TermElabM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let .ok root ← goalStartExpr "True" #[] | throwError "start failed"
  for tactic in placeholderTactics do
    let result ← (runTermElabM (root.tryTactic root.root tactic) : CoreM _)
    tests := tests ++ LSpec.test s!"{tactic} is an ordinary failure with Lean's own message"
      (failsWith "don't know how to synthesize placeholder" result)
  -- The rejected candidate leaves the input state usable for the next one.
  let .success done ← (runTermElabM (root.tryTactic root.root "trivial") : CoreM _) | throwError "trivial failed"
  tests := tests ++ LSpec.test "the input state still proves the goal after the failures"
    ((← validateTransition root done root.root).toOption.isSome &&
      (← certifyRoot done 200000).status == "certified")
  return tests

private def boundTests : LSpec.TestSeq :=
  let huge := String.join (List.replicate 4000 "∀\"\\\n")
  let evidence : Repl.FailureEvidence := { sequence := 7, operation := "goal.tactic", stateId := some 3, goalIndex := some 0, phase := "observe", category := "error", detail := some huge }
  let line := evidence.line
  let parsed := Json.parse line
  let field (key : String) := parsed.toOption.bind fun j => (j.getObjVal? key).toOption
  let unrendered : Repl.FailureEvidence := { sequence := 1, operation := "goal.certify", category := "internal", internalId := some "x", detail := none }
  let failed := unrendered.line
  LSpec.test "a huge escaped detail is cut so the whole line stays within the byte limit"
      (line.utf8ByteSize ≤ Repl.diagnosticLineBytes && parsed.toOption.isSome) ++
    LSpec.test "the record says the detail was truncated"
      (field "detail_truncated" == some (Json.bool true) && field "kind" == some (Json.str "pantograph-command-failure")) ++
    LSpec.test "a failed rendering is reported, not invented"
      ((Json.parse failed).toOption.any fun j =>
        (j.getObjVal? "render_status").toOption == some (Json.str "failed") && (j.getObjVal? "detail").toOption == some Json.null)

def suite (env : Environment) : List (String × IO LSpec.TestSeq) := [
  ("Elaboration aborts", runTermElabMSeq env abortTests),
  ("Diagnostic bounds", pure boundTests)
]

end Pantograph.Test.FailureBoundary
