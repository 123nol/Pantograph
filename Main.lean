import Lean.Data.Json
import Lean.Environment

import Pantograph
import Repl

-- Main IO functions
open Pantograph.Repl
open Pantograph.Protocol

/-- Parse a command either in `{ "cmd": ..., "payload": ... }` form or `cmd { ... }` form. -/
def parseCommand (s: String): Except String Command := do
  let s := s.trim
  match s.get? 0 with
  | .some '{' => -- Parse in Json mode
    Lean.fromJson? (← Lean.Json.parse s)
  | .some _ => -- Parse in line mode
    let offset := s.posOf ' ' |> s.offsetOfPos
    if offset = s.length then
      return { cmd := s.take offset, payload := Lean.Json.null }
    else
      let payload ← s.drop offset |> Lean.Json.parse
      return { cmd := s.take offset, payload := payload }
  | .none => throw "Command is empty"

/-- A failed write ends the process; it never triggers a second response. -/
def writeResponse (bytes : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr (bytes ++ "\n")
  stdout.flush

partial def loop : MainM UInt32 := do
  let command ← (← IO.getStdin).getLine
  if command.trim.length = 0 then return (0 : UInt32)
  match parseCommand command with
  | .error error =>
    let error := Lean.toJson ({ error := "command", desc := error.take 2048 } : InteractionError)
    writeResponse error.compress
  | .ok command =>
    let result ← executeCommand command
    writeResponse result.bytes
    if result.fatal then
      (← IO.getStderr).putStrLn "REPL command failed; session is unusable"
      return (1 : UInt32)
  loop

private unsafe def runRepl (args: List String): IO UInt32 := do
  -- NOTE: A more sophisticated scheme of command line argument handling is needed.
  -- Separate imports and options
  if args == ["--version"] then do
    println! s!"{Pantograph.version}"
    return (0 : UInt32)

  Pantograph.initSearch ""

  let coreContext ← args.filterMap (λ s => if s.startsWith "--" then .some <| s.drop 2 else .none)
    |>.toArray |> Pantograph.createCoreContext
  let imports:= args.filter (λ s => ¬ (s.startsWith "--"))
  let coreState ← Pantograph.createCoreState imports.toArray
  let context: Context := {
    imports
  }
  let coreM := loop.run context |>.run' {}
  writeResponse "ready."
  return (← coreM.toIO coreContext coreState).1

unsafe def main (args : List String) : IO UInt32 := do
  try
    runRepl args
  catch _ =>
    (← IO.getStderr).putStrLn "REPL startup or transport failure; session is unusable"
    return (1 : UInt32)
