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

/-- Keep resource and unexpected internal exceptions out of ordinary user diagnostics. -/
def rethrowInfrastructure [Monad m] [MonadExceptOf Exception m] (ex : Exception) : m Unit := do
  match ex with
  | .internal .. => throw ex
  | _ => if ex.isRuntime then throw ex

private def phaseCore (phase : String) (action : CoreM α) : CoreM α := do
  tryCatchRuntimeEx (do
    Core.checkMaxHeartbeats "pantograph"
    let result ← action
    Core.checkMaxHeartbeats "pantograph"
    return result) fun ex => do
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
