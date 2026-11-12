import Lean

namespace Pantograph
open Lean

register_option pantograph.traceCommands : Bool := {
  defValue := false
  descr := "write bounded REPL request and outcome traces to stderr"
}

/-- A command exhausted a Lean resource limit (heartbeats or recursion depth).
    The kind, phase and limit are attached before unwinding restores goal contexts. -/
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

/-- The innermost phase the propagating exception left, with that exception.
    An outer phase keeps the record only for the same exception object, so a
    handled exception cannot lend its phase to a later, different one. -/
builtin_initialize failedCommandPhase : IO.Ref (Option (String × Exception)) ← IO.mkRef none

private unsafe def sameExceptionImpl (a b : Exception) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Object identity: the record holds its exception, so the address cannot be reused. -/
@[implemented_by sameExceptionImpl]
private opaque sameException (a b : Exception) : Bool

/-- The phase `ex` was recorded in, or `unknown` if no phase saw this exception. -/
def failurePhase (ex : Exception) : IO String := do
  match ← failedCommandPhase.get with
  | some (phase, recorded) => return if sameException recorded ex then phase else "unknown"
  | none => return "unknown"

/-- The limit of the innermost `set_option … in` scope that a recursion-depth
    exception left, with that exception. The scope's context has unwound by the
    time the phase boundary sees the exception, so the scope records its own. -/
builtin_initialize scopedRecursionLimit : IO.Ref (Option (Nat × Exception)) ← IO.mkRef none

/-- The limit a `set_option maxRecDepth N in` scope applies; `none` for other options,
    which leave the recursion limit unchanged. Lean requires a numeric literal here. -/
private def scopeLimit (stx : Syntax) : Option Nat :=
  if stx[1].getId.eraseMacroScopes == `maxRecDepth then stx[3].isNatLit? else none

/-- Run a `set_option … in` scope; if a recursion-depth exception leaves a scope
    that sets `maxRecDepth` and no inner scope recorded it, record this limit. -/
private def recordingScopedLimit [Monad m] [MonadControlT CoreM m]
    (stx : Syntax) (scope : m α) : m α :=
  match scopeLimit stx with
  | none => scope
  | some limit => controlAt CoreM fun run => tryCatchRuntimeEx (run scope) fun ex => do
    if ex.isMaxRecDepth then
      let recorded := match ← scopedRecursionLimit.get with
        | some (_, previous) => sameException previous ex
        | none => false
      unless recorded do scopedRecursionLimit.set (some (limit, ex))
    throw ex

/-- Wrap Lean's tactic and term `set_option … in` elaborators in place, so each
    still has exactly one elaborator and ordinary failures are unchanged. -/
builtin_initialize do
  Elab.Tactic.tacticElabAttribute.tableRef.modify fun table =>
    match table.find? ``Lean.Parser.Tactic.set_option with
    | some entries => table.insert ``Lean.Parser.Tactic.set_option <| entries.map fun entry =>
        { entry with value := fun stx => recordingScopedLimit stx (entry.value stx) }
    | none => table
  Elab.Term.termElabAttribute.tableRef.modify fun table =>
    match table.find? ``Lean.Parser.Term.set_option with
    | some entries => table.insert ``Lean.Parser.Term.set_option <| entries.map fun entry =>
        { entry with value := fun stx expected? => recordingScopedLimit stx (entry.value stx expected?) }
    | none => table

private def phaseCore (phase : String) (action : CoreM α) : CoreM α := do
  tryCatchRuntimeEx (do
    Core.checkMaxHeartbeats "pantograph"
    let result ← action
    Core.checkMaxHeartbeats "pantograph"
    return result) fun ex => do
      let innermost := match ← failedCommandPhase.get with
        | some (_, recorded) => !sameException recorded ex
        | none => true
      if innermost then failedCommandPhase.set (some (phase, ex))
      let ctx ← read
      let resource (kind : String) (limit : Nat) : Exception :=
        .internal commandResourceExceptionId <|
          ({} : KVMap).setString `kind kind |>.setString `phase phase |>.setNat `limit limit
      let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
      if ex.isMaxHeartbeat && ctx.maxHeartbeats > 0 && used > ctx.maxHeartbeats then
        throw <| resource "heartbeats" (ctx.maxHeartbeats / 1000)
      -- Lean's own predicate for `throwMaxRecDepthAt`. The limit is the innermost
      -- `set_option … in` scope's, recorded for this exception, or else this
      -- command's configured `maxRecDepth`, in nesting levels.
      if ex.isMaxRecDepth then
        let limit := match ← scopedRecursionLimit.get with
          | some (inner, recorded) => if sameException recorded ex then inner else ctx.maxRecDepth
          | none => ctx.maxRecDepth
        if limit > 0 then
          throw <| resource "recursion-depth" limit
      throw ex

/-- Account for work before and after each protected phase without resetting its budget. -/
def withCommandPhase [Monad m] [MonadControlT CoreM m] (phase : String) (action : m α) : m α :=
  controlAt CoreM fun run => phaseCore phase (run action)

end Pantograph
