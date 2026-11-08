import Lean

namespace Pantograph
open Lean

register_option pantograph.traceCommands : Bool := {
  defValue := false
  descr := "write bounded REPL request and outcome traces to stderr"
}

/-- The phase is attached before unwinding restored goal contexts. -/
builtin_initialize commandResourceExceptionId : InternalExceptionId ←
  registerInternalExceptionId `pantographCommandResource

/-- Lean's elaborator logs an error and then aborts the term, tactic or command.
    The abort carries no message of its own; it is an ordinary elaboration failure. -/
def isElaborationAbort : Exception → Bool
  | .internal id _ => Elab.isAbortExceptionId id
  | _ => false

/-- Keep resource and unexpected internal exceptions out of ordinary user diagnostics.
    Elaboration aborts are ordinary failures whose error is already in the message log. -/
def rethrowInfrastructure [Monad m] [MonadExceptOf Exception m] (ex : Exception) : m Unit := do
  match ex with
  | .internal .. => unless isElaborationAbort ex do throw ex
  | _ => if ex.isRuntime then throw ex

/-- Text of an ordinary elaboration failure. An abort's text is the error it logged. -/
def failureText (ex : Exception) : CoreM String := do
  unless isElaborationAbort ex do return ← ex.toMessageData.toString
  let errors := (← getThe Core.State).messages.toList.filter (·.severity == .error)
  if errors.isEmpty then return "Lean aborted elaboration after reporting an error"
  return "\n".intercalate (← errors.mapM (·.data.toString))

/-- The innermost phase an exception last left, cleared whenever a phase starts.
    Read at the transaction boundary after unwinding; `none` means no phase saw it. -/
builtin_initialize failedCommandPhase : IO.Ref (Option String) ← IO.mkRef none

private def phaseCore (phase : String) (action : CoreM α) : CoreM α := do
  failedCommandPhase.set none
  tryCatchRuntimeEx (do
    Core.checkMaxHeartbeats "pantograph"
    let result ← action
    Core.checkMaxHeartbeats "pantograph"
    return result) fun ex => do
      if (← failedCommandPhase.get).isNone then failedCommandPhase.set (some phase)
      let ctx ← read
      let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
      if ex.isMaxHeartbeat && ctx.maxHeartbeats > 0 && used > ctx.maxHeartbeats then
        throw <| .internal commandResourceExceptionId <|
          ({} : KVMap).setString `phase phase |>.setNat `limit (ctx.maxHeartbeats / 1000)
      throw ex

/-- Account for work before and after each protected phase without resetting its budget. -/
def withCommandPhase [Monad m] [MonadControlT CoreM m] (phase : String) (action : m α) : m α :=
  controlAt CoreM fun run => phaseCore phase (run action)

end Pantograph
