import Pantograph.Protocol
import Lean

namespace Pantograph
open Lean

private def messageKind : MessageData → Name
  | .tagged name _ => name
  | .withContext _ data | .withNamingContext _ data | .nest _ data
  | .group data | .ofWidget _ data => messageKind data
  | _ => .anonymous

/-- Elaborate source strings against their actual source map. -/
def withInputContext (input : String) (action : Elab.TermElabM α) : Elab.TermElabM α :=
  withTheReader Core.Context (fun ctx =>
    { ctx with fileName := "<pantograph>", fileMap := input.toFileMap }) action

/-- Render diagnostics without introducing source locations absent from Lean. -/
def renderMessages (log : MessageLog) : CoreM (Array Protocol.Message) := do
  log.toArray.mapM fun message => do
    let context ← read
    let known := message.pos.line > 0 && !context.fileMap.source.isEmpty && message.fileName == context.fileName
    let pos : Protocol.MessagePos := if known then
      { line := message.pos.line, column := message.pos.column } else {}
    let endPos? := message.endPos.bind fun p =>
      if known && (p.line > pos.line || (p.line == pos.line && p.column >= pos.column)) then
        some { line := p.line, column := p.column } else none
    return {
      kind := (messageKind message.data).toString,
      severity := match message.severity with
        | .information => "information"
        | .warning => "warning"
        | .error => "error",
      pos, endPos?, data := ← message.data.toString
    }

private def convSequence : Parser.Parser :=
  Parser.node ``Parser.Tactic.Conv.convSeq <|
    (Parser.node ``Parser.Tactic.Conv.convSeqBracketed <|
      Parser.symbol "{" >> Parser.withoutPosition
        (Parser.Tactic.sepByIndentSemicolon (Parser.categoryParser `conv 0)) >> Parser.symbol "}") <|>
    (Parser.node ``Parser.Tactic.Conv.convSeq1Indented <|
      Parser.Tactic.sepBy1IndentSemicolon (Parser.categoryParser `conv 0))

/-- Parse a full selected-mode sequence, including the final end-of-input check. -/
def parseTacticSequence (env : Environment) (isConv : Bool) (input : String) : Except String Syntax :=
  let parser := if isConv then convSequence else Parser.Tactic.tacticSeq
  let context := Parser.mkInputContext input "<pantograph>"
  let state := (Parser.andthenFn Parser.whitespace parser.fn).run context
    { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState input)
  if !state.allErrors.isEmpty then
    .error (state.toErrorMsg context)
  else if context.input.atEnd state.pos then
    .ok state.stxStack.back
  else
    .error ((state.mkError "end of input").toErrorMsg context)

end Pantograph
