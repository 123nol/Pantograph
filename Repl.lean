import Lean.Data.HashMap
import Pantograph
import Pantograph.Validation
import Pantograph.Transition
import Pantograph.Certify

namespace Pantograph.Repl

structure Context where
  imports: List String

/-- Stores state of the REPL -/
structure State where
  usable : Bool := true
  /-- Commands this process has dispatched; numbers its failure diagnostics. -/
  commandSequence : Nat := 0
  options: Protocol.Options := {}
  nextId: Nat := 0
  goalStates: Lean.HashMap Nat GoalState := Lean.HashMap.empty

/-- Main state monad for executing commands -/
abbrev MainM := ReaderT Context (StateT State Lean.CoreM)

-- HACK: For some reason writing `CommandM α := MainM (Except ... α)` disables
-- certain monadic features in `MainM`
abbrev CR α := Except Protocol.InteractionError α

def runMetaInMainM { α } (metaM: Lean.MetaM α): MainM α :=
  metaM.run'
def runTermElabInMainM { α } (termElabM: Lean.Elab.TermElabM α) : MainM α :=
  termElabM.run' (ctx := Condensed.elabContext) |>.run'

private def dispatch (command: Protocol.Command): MainM Lean.Json := do
  let run { α β: Type } [Lean.FromJson α] [Lean.ToJson β] (comm: α → MainM (CR β)): MainM Lean.Json :=
    match Lean.fromJson? command.payload with
    | .ok args => do
      match (← comm args) with
      | .ok result => withCommandPhase "serialize" <| pure (Lean.toJson result)
      | .error ierror => withCommandPhase "serialize" <| pure (Lean.toJson ierror)
    | .error error => return Lean.toJson $ errorCommand s!"Unable to parse json: {error}"
  match command.cmd with
  | "protocol.describe" => run protocol_describe
  | "reset"         => run reset
  | "stat"          => run stat
  | "expr.echo"     => run expr_echo
  | "env.catalog"   => run env_catalog
  | "env.inspect"   => run env_inspect
  | "env.add"       => run env_add
  | "options.set"   => run options_set
  | "options.print" => run options_print
  | "goal.start"    => run goal_start
  | "goal.tactic"   => run goal_tactic
  | "goal.continue" => run goal_continue
  | "goal.delete"   => run goal_delete
  | "goal.inspect"  => run goal_inspect
  | "goal.certify"  => run goal_certify
  | "goal.print"    => run goal_print
  | "frontend.process"  => run frontend_process
  | cmd =>
    let error: Protocol.InteractionError :=
      errorCommand s!"Unknown command {cmd}"
    return Lean.toJson error
  where
  errorCommand := errorI "command"
  errorIndex := errorI "index"
  newGoalState (goalState: GoalState) : MainM Nat := do
    let goalState := (← requireValidation (validateSnapshot goalState)).state
    let state ← get
    let stateId := state.nextId
    set { state with
      goalStates := state.goalStates.insert stateId goalState,
      nextId := state.nextId + 1
    }
    return stateId
  protocol_describe (_ : Protocol.ProtocolDescribe) : MainM (CR Protocol.ProtocolDescriptor) :=
    pure (.ok {})
  -- Command Functions
  reset (_: Protocol.Reset): MainM (CR Protocol.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    set { state with nextId := 0, goalStates := Lean.HashMap.empty }
    return .ok { nGoals }
  stat (_: Protocol.Stat): MainM (CR Protocol.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    return .ok { nGoals }
  env_catalog (args: Protocol.EnvCatalog): MainM (CR Protocol.EnvCatalogResult) := do
    let result ← withCommandPhase "observe" <| Environment.catalog args
    return .ok result
  env_inspect (args: Protocol.EnvInspect): MainM (CR Protocol.EnvInspectResult) := do
    let state ← get
    withCommandPhase "observe" <| Environment.inspect args state.options
  env_add (args: Protocol.EnvAdd): MainM (CR Protocol.EnvAddResult) := do
    Environment.addDecl args
  expr_echo (args: Protocol.ExprEcho): MainM (CR Protocol.ExprEchoResult) := do
    let state ← get
    exprEcho args.expr (expectedType? := args.type?) (levels := args.levels.getD #[]) (options := state.options)
  options_set (args: Protocol.OptionsSet): MainM (CR Protocol.OptionsSetResult) := do
    let state ← get
    let options := state.options
    set { state with
      options := {
        -- FIXME: This should be replaced with something more elegant
        printExprPretty := args.printExprPretty?.getD options.printExprPretty,
        printExprAST := args.printExprAST?.getD options.printExprAST,
        printExprModelAST := args.printExprModelAST?.getD options.printExprModelAST,
        printDependentMVars := args.printDependentMVars?.getD options.printDependentMVars,
        noRepeat := args.noRepeat?.getD options.noRepeat,
        printAuxDecls := args.printAuxDecls?.getD options.printAuxDecls,
        printImplementationDetailHyps := args.printImplementationDetailHyps?.getD options.printImplementationDetailHyps
        automaticMode := args.automaticMode?.getD options.automaticMode,
      }
    }
    return .ok {  }
  options_print (_: Protocol.OptionsPrint): MainM (CR Protocol.Options) := do
    return .ok (← get).options
  goal_start (args: Protocol.GoalStart): MainM (CR Protocol.GoalStartResult) := do
    let env ← Lean.MonadEnv.getEnv
    let expr?: Except _ GoalState ← runTermElabInMainM (match args.expr, args.copyFrom with
      | .some expr, .none => goalStartExpr expr (args.levels.getD #[])
      | .none, .some copyFrom =>
        (match env.find? <| copyFrom.toName with
        | .none => return .error <| errorIndex s!"Symbol not found: {copyFrom}"
        | .some cInfo => return .ok { (← GoalState.create cInfo.type) with rootLevels := cInfo.levelParams })
      | _, _ =>
        return .error <| errorI "arguments" "Exactly one of {expr, copyFrom} must be supplied")
    match expr? with
    | .error error => return .error error
    | .ok goalState =>
      let stateId ← newGoalState goalState
      return .ok { stateId, root := goalState.root.name.toString }
  goal_tactic (args: Protocol.GoalTactic): MainM (CR Protocol.GoalTacticResult) := do
    let state ← get
    let .some goalState := state.goalStates.find? args.stateId |
      return .error $ errorIndex s!"Invalid state index {args.stateId}"
    let conv? : Option Bool := match args.conv?, args.mode? with
      | .some b, _ => .some b
      | .none, .some "conv" => .some true
      | .none, .some "tactic" => if goalState.convMVar?.isSome then .some false else .none
      | .none, _ => .none
    let isConvExit := conv? == .some false
    let goalId := args.goalId?.getD 0
    let goal? := goalState.goals.get? goalId
    if !isConvExit && goal?.isNone then
      return .error $ errorIndex s!"Invalid goal index {goalId}"
    -- Conv exit ignores goalId and remains valid after its final inner goal closes.
    let goal := goal?.getD goalState.root
    let autoMode := args.autoResume?.getD state.options.automaticMode
    let nextGoalState?: Except _ TacticResult ← runTermElabInMainM do
      let finalize (result : TacticResult) : Lean.Elab.TermElabM TacticResult := do
        let .success nextGoalState := result | pure result
        if goalState.convMVar?.isNone || nextGoalState.convMVar?.isNone then
          return result
        let siblingGoals := goalState.goals.filter (· != goal)
        let .ok resumedState := nextGoalState.resume (nextGoalState.goals ++ siblingGoals) |
          return .invalidAction "Failed to resume conversion goals"
        if !resumedState.goals.isEmpty then
          return if autoMode then .success resumedState else result
        match ← resumedState.convExit with
        | .success exitedState =>
          let exitedState := { exitedState with messages := nextGoalState.messages ++ exitedState.messages }
          if autoMode then
            let dormantGoals := goalState.convMVar?.map (fun (_, _, goals) => goals) |>.getD []
            match exitedState.resume (exitedState.goals ++ dormantGoals) with
            | .ok resumedState => pure <| .success resumedState
            | .error error => pure <| .invalidAction error
          else
            pure <| .success exitedState
        | other => pure other
      match args.tactic?, args.expr?, args.have?, args.let?, args.calc?, args.conv?, args.mode? with
      | .some tactic, .none, .none, .none, .none, .none, .none => do
        pure <| Except.ok <| ← finalize <| ← goalState.tryTactic goal tactic
      | .none, .some expr, .none, .none, .none, .none, .none => do
        pure <| Except.ok <| ← finalize <| ← goalState.tryAssign goal expr
      | .none, .none, .some type, .none, .none, .none, .none => do
        let binderName := args.binderName?.getD ""
        pure <| Except.ok <| ← finalize <| ← goalState.tryHave goal binderName type
      | .none, .none, .none, .some type, .none, .none, .none => do
        let binderName := args.binderName?.getD ""
        pure <| Except.ok <| ← finalize <| ← goalState.tryLet goal binderName type
      | .none, .none, .none, .none, .some pred, .none, .none => do
        pure <| Except.ok <| ← finalize <| ← goalState.tryCalc goal pred
      | .none, .none, .none, .none, .none, .some true, .none
      | .none, .none, .none, .none, .none, .none, .some "conv" => do
        pure <| Except.ok <| ← finalize <| ← goalState.conv goal
      | .none, .none, .none, .none, .none, .some false, .none
      | .none, .none, .none, .none, .none, .none, .some "tactic" => do
        pure <| Except.ok <| ← finalize <| ← goalState.convExit
      | .none, .none, .none, .none, .none, .none, .some "calc" => do
        pure <| Except.ok <| .invalidAction "calc mode is entered via 'calc' parameter with a step predicate, not via 'mode'"
      | _, _, _, _, _, _, _ =>
        let error := errorI "arguments" "Exactly one of {tactic, expr, have, let, calc, conv, mode} must be supplied"
        pure $ Except.error $ error
    match nextGoalState? with
    | .error error => return .error error
    | .ok (.success nextGoalState) => do
      let produced := nextGoalState.goals
      let nextGoalState ← match autoMode, isConvExit with
        | true, false => do
          if goalState.convMVar?.isNone && nextGoalState.convMVar?.isNone then
            let .ok result := nextGoalState.resume (nextGoalState.goals ++ goalState.goals) | throwError "Resuming known goals"
            pure result
          else
            pure nextGoalState
        | true, true => do
          let .some (_, _, dormantGoals) := goalState.convMVar? | throwError "If conv exit succeeded this should not fail"
          let .ok result := nextGoalState.resume (nextGoalState.goals ++ dormantGoals) | throwError "Resuming known goals"
          pure result
        | false, _ => pure nextGoalState
      let checked ← requireValidation (validateTransition goalState nextGoalState goal)
      let nextGoalState := checked.state
      let goals ← withCommandPhase "observe" <| nextGoalState.serializeGoals (parent := .some goalState) (options := state.options) |>.run'
      let transition ← withCommandPhase "observe" <| pure (transitionProvenance state.options goalState nextGoalState goal produced)
      let nextStateId ← newGoalState nextGoalState
      return .ok {
        nextStateId? := .some nextStateId,
        goals? := .some goals,
        messages := nextGoalState.messages,
        hasSorry := checked.hasSorry,
        hasUnsafe := checked.hasUnsafe,
        validation? := some { checked := true },
        transition? := some transition,
      }
    | .ok (.parseError message) =>
      return .ok {
        parseError? := .some message,
        messages := #[Protocol.Message.error message],
      }
    | .ok (.invalidAction message) =>
      return .error $ errorI "invalid" message
    | .ok (.failure messages diagnostics) =>
      return .ok {
        tacticErrors? := .some messages,
        messages := diagnostics,
      }
  goal_continue (args: Protocol.GoalContinue): MainM (CR Protocol.GoalContinueResult) := do
    let state ← get
    let .some target := state.goalStates.find? args.target | return .error $ errorIndex s!"Invalid state index {args.target}"
    let nextState? ← match args.branch?, args.goals? with
      | .some branchId, .none => do
        match state.goalStates.find? branchId with
        | .none => return .error $ errorIndex s!"Invalid state index {branchId}"
        | .some branch => pure $ target.continue branch
      | .none, .some goals =>
        pure $ goalResume target goals
      | _, _ => return .error <| errorI "arguments" "Exactly one of {branch, goals} must be supplied"
    match nextState? with
    | .error error => return .error <| errorI "structure" error
    | .ok nextGoalState =>
      let nextStateId ← newGoalState nextGoalState
      let goals ← withCommandPhase "observe" <| goalSerialize nextGoalState (options := state.options)
      return .ok {
        nextStateId,
        goals,
      }
  goal_delete (args: Protocol.GoalDelete): MainM (CR Protocol.GoalDeleteResult) := do
    let state ← get
    let goalStates := args.stateIds.foldl (λ map id => map.erase id) state.goalStates
    set { state with goalStates }
    return .ok {}
  goal_inspect (args: Protocol.GoalInspect): MainM (CR Protocol.GoalInspectResult) := do
    let state ← get
    let .some goalState := state.goalStates.find? args.stateId |
      return .error $ errorIndex s!"Invalid state index {args.stateId}"
    if args.goals.isEmpty || args.goals.toList.eraseDups.length != args.goals.size then
      return .error <| errorI "arguments" "goals must be a nonempty list of distinct names"
    let mut obligations := #[]
    for name in args.goals do
      let some obligation ← withCommandPhase "observe" <| runMetaInMainM <| inspectObligation goalState ⟨name.toName⟩ state.options |
        return .error $ errorIndex s!"Unknown obligation {name}"
      obligations := obligations.push obligation
    let published := { goalState with publishedObligations :=
      (goalState.publishedObligations ++ args.goals.toList.map (fun name => (⟨name.toName⟩ : Lean.MVarId))).eraseDups }
    set { state with goalStates := state.goalStates.insert args.stateId published }
    return .ok { obligations }
  goal_certify (args: Protocol.GoalCertify): MainM (CR Protocol.GoalCertifyResult) := do
    let state ← get
    let .some goalState := state.goalStates.find? args.stateId |
      return .error $ errorIndex s!"Invalid state index {args.stateId}"
    let maxHeartbeats := args.maxHeartbeats?.getD 200000
    if maxHeartbeats == 0 then
      return .error <| errorI "arguments" "maxHeartbeats must be positive"
    discard <| requireValidation (validateSnapshot goalState)
    return .ok (← certifyRoot goalState maxHeartbeats)
  goal_print (args: Protocol.GoalPrint): MainM (CR Protocol.GoalPrintResult) := do
    let state ← get
    let .some goalState := state.goalStates.find? args.stateId | return .error $ errorIndex s!"Invalid state index {args.stateId}"
    let result ← withCommandPhase "observe" <| runMetaInMainM <| goalPrint goalState state.options
    return .ok result
  frontend_process (args: Protocol.FrontendProcess): MainM (CR Protocol.FrontendProcessResult) := do
    let options := (← get).options
    let (fileName, file) ← match args.fileName?, args.file? with
      | .some fileName, .none => do
        let file ← IO.FS.readFile fileName
        pure (fileName, file)
      | .none, .some file =>
        pure ("<anonymous>", file)
      | _, _ => return .error <| errorI "arguments" "Exactly one of {fileName, file} must be supplied"
    let env?: Option Lean.Environment ← if args.fileName?.isSome then
        pure .none
      else do
        let env ← Lean.MonadEnv.getEnv
        pure <| .some env
    let (context, state) ← do Frontend.createContextStateFromFile file fileName env? (← Lean.getOptions)
    let li ← Frontend.mapCompilationSteps context state λ step => do
      let boundary := (step.src.startPos.byteIdx, step.src.stopPos.byteIdx)
      let invocations?: Option (List Protocol.InvokedTactic) ← if args.invocations then
          let invocations ← Frontend.collectTacticsFromCompilationStep step options
          pure $ .some invocations
        else
          pure .none
      let sorrys := if args.sorrys then
          Frontend.collectSorrys step
        else
          []
      let messages ← step.messageStrings
      return (boundary, invocations?, sorrys, messages)
    let units ← withCommandPhase "observe" <| li.mapM λ (boundary, invocations?, sorrys, messages) => do
      let (goalStateId?, goals) ← if sorrys.isEmpty then do
          pure (.none, #[])
        else do
          let goalState ← runMetaInMainM $ Frontend.sorrysToGoalState sorrys
          let stateId ← newGoalState goalState
          let goals ← goalSerialize goalState options
          pure (.some stateId, goals)
      return {
        boundary,
        invocations?,
        goalStateId?,
        goals,
        messages,
      }
    let result : Protocol.FrontendProcessResult := { units }
    if let some outputFile := args.outputFile? then
      IO.FS.writeFile outputFile (Lean.Json.compress (Lean.toJson result))
      return .ok { units := [] }
    else
      return .ok result

/-- Bytes are fully encoded before the staged states become visible. -/
structure CommandResult where
  response : Lean.Json
  bytes : String
  fatal : Bool := false

/-- Byte bounds of the fatal stderr diagnostic. -/
def diagnosticDetailBytes : Nat := 2048
def diagnosticLineBytes : Nat := 4096

private def takeBytesAux (limit : Nat) : List Char → Nat → List Char
  | [], _ => []
  | c :: cs, used =>
    let size := (String.singleton c).utf8ByteSize
    if used + size > limit then [] else c :: takeBytesAux limit cs (used + size)

/-- The longest prefix of `text` that fits in `limit` UTF-8 bytes. -/
def takeBytes (text : String) (limit : Nat) : String :=
  String.mk (takeBytesAux limit text.toList 0)

/-- Render an exception's message. Rendering can itself fail; that is reported, not raised.
    Lean's pretty-printer applies its own default heartbeat limit inside the message. -/
private def renderException (ex : Lean.Exception) : IO (Option String) := do
  try
    return some (← ex.toMessageData.toString)
  catch _ => return none

/-- What the transaction boundary knows about an unexpected fatal failure. -/
structure FailureEvidence where
  sequence : Nat
  operation : String
  stateId : Option Nat := none
  goalIndex : Option Nat := none
  phase : String := "unknown"
  category : String
  internalId : Option String := none
  /-- The rendered exception message, or `none` when rendering failed. -/
  detail : Option String := none

/-- The version-1 diagnostic line: kind `pantograph-command-failure`, at most
    `diagnosticLineBytes` bytes including JSON escaping. The detail is cut first. -/
def FailureEvidence.line (e : FailureEvidence) : String := Id.run do
  let full := e.detail.getD ""
  let record (detail? : Option String) : Lean.Json := Lean.Json.mkObj [
    ("kind", "pantograph-command-failure"), ("version", (1 : Nat)),
    ("repl_command_sequence", e.sequence), ("operation", takeBytes e.operation 64),
    ("state_id", Lean.toJson e.stateId), ("goal_index", Lean.toJson e.goalIndex),
    ("phase", takeBytes e.phase 32), ("exception_category", e.category),
    ("internal_exception_id", Lean.toJson (e.internalId.map (takeBytes · 256))),
    ("detail", Lean.toJson detail?),
    ("detail_truncated", Lean.toJson (e.detail.isSome && (detail?.getD "").utf8ByteSize < full.utf8ByteSize)),
    ("render_status", if e.detail.isSome then "rendered" else "failed")]
  let mut limit := diagnosticDetailBytes
  let mut line := (record (e.detail.map fun _ => takeBytes full limit)).compress
  while line.utf8ByteSize > diagnosticLineBytes && limit > 0 do
    limit := limit / 2
    line := (record (if limit == 0 then none else e.detail.map fun _ => takeBytes full limit)).compress
  return line

/-- One bounded JSON line on stderr for an unexpected fatal command failure.
    Stdout, recovery and session fatality are unchanged; a failed write is ignored. -/
private def writeFailureDiagnostic (command : Protocol.Command) (sequence : Nat)
    (ex : Lean.Exception) : IO Unit := do
  try
    let (category, internalId) ← match ex with
      | .internal id _ => pure ("internal", some (← id.getName).toString)
      | .error .. => pure (if ex.isRuntime then "runtime" else "error", none)
    let nat (key : String) := command.payload.getObjValAs? Nat key |>.toOption
    let evidence : FailureEvidence := {
      sequence, operation := command.cmd, phase := ← failurePhase ex,
      stateId := (nat "stateId").orElse fun _ => nat "target", goalIndex := nat "goalId",
      category, internalId, detail := ← renderException ex }
    let stderr ← IO.getStderr
    stderr.putStrLn evidence.line
    stderr.flush
  catch _ => pure ()

/-- A separate Core state reference owns all changes until encoding completes.
    Failure discards that reference; restoration requires no Lean computation. -/
def runTransaction (command : Protocol.Command) (action : MainM Lean.Json) : MainM CommandResult := do
  modify fun s => { s with commandSequence := s.commandSequence + 1 }
  failedCommandPhase.set none
  let entry ← get
  let coreEntry ← getThe Lean.Core.State
  let ctx ← read
  let coreCtx ← readThe Lean.Core.Context
  let fail (error desc recovery : String) (resource? : Option Protocol.ResourceDetails := none) : CommandResult :=
    let response := Lean.toJson ({ error, desc, resource?, recovery } : Protocol.CommandFailure)
    { response, bytes := response.compress, fatal := recovery == "session-unusable" }
  unless entry.usable do
    return fail "internal" "Unexpected REPL command failure" "session-unusable"
  let stagedAction : Lean.CoreM ((Lean.Json × String) × State) := Lean.withCurrHeartbeats do
    withCommandPhase "execute" <| (do
      let response ← action
      let bytes ← withCommandPhase "serialize" <| pure response.compress
      return (response, bytes)).run ctx |>.run entry
  let started ← IO.getNumHeartbeats
  let outcome ← (stagedAction.run coreCtx coreEntry).toBaseIO
  if pantograph.traceCommands.get coreCtx.options then
    let phase := match outcome with
      | .error (.internal _ details) => details.getString `phase "unknown"
      | _ => "complete"
    let text := command.payload.getObjValAs? String "tactic" |>.toOption |>.getD ""
    let selected := command.payload.getObjValAs? Nat "stateId" |>.toOption
    let goal := command.payload.getObjValAs? Nat "goalId" |>.toOption
    let trace := Lean.Json.mkObj [
      ("command", .str (command.cmd.take 128)), ("tactic", .str (text.take 512)),
      ("stateId", Lean.toJson selected), ("goalId", Lean.toJson goal),
      ("phase", .str phase), ("heartbeats", Lean.toJson ((← IO.getNumHeartbeats) - started))]
    (← IO.getStderr).putStrLn trace.compress
  match outcome with
  | .ok (((response, bytes), staged), coreStaged) =>
    set staged
    modifyThe Lean.Core.State fun _ => coreStaged
    return { response, bytes }
  | .error ex =>
    let result := match ex with
      | .internal id details =>
        if id == validationExceptionId then
          let response := Lean.toJson ({ error := "validation", desc := details.getString `desc } : Protocol.InteractionError)
          { response, bytes := response.compress, fatal := true }
        else if id == commandResourceExceptionId && details.getNat `limit > 0 &&
            ["execute", "validate", "observe", "serialize"].contains (details.getString `phase) &&
            ["heartbeats", "recursion-depth"].contains (details.getString `kind) then
          let kind := details.getString `kind
          let desc := if kind == "heartbeats" then "Lean command heartbeat budget exhausted"
            else "Lean maximum recursion depth reached"
          if command.cmd == "goal.certify" then
            let response := Lean.toJson ({
              status := "inconclusive", reason? := some desc } : Protocol.GoalCertifyResult)
            { response, bytes := response.compress }
          else
            -- Frontend imports and output files may have effects outside retained Lean state.
            fail "resource" desc
              (if command.cmd == "frontend.process" then "session-unusable" else "command-rolled-back")
              (some { kind, phase := details.getString `phase, limit := details.getNat `limit })
        else fail "internal" "Unexpected REPL command failure" "session-unusable"
      | _ => fail "internal" "Unexpected REPL command failure" "session-unusable"
    if (Lean.Json.getObjValAs? result.response String "error").toOption == some "internal" then
      writeFailureDiagnostic command entry.commandSequence ex
    set { entry with usable := !result.fatal }
    return result

/-- Every dispatch path uses the same transaction and encoding boundary. -/
def executeCommand (command : Protocol.Command) : MainM CommandResult :=
  runTransaction command (dispatch command)

/-- Native callers share the executable's transaction boundary. -/
def execute (command : Protocol.Command) : MainM Lean.Json := do
  return (← executeCommand command).response

end Pantograph.Repl
