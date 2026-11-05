import Pantograph.Goal

namespace Pantograph
open Lean

inductive ValidationPurpose where
  | execution
  | auxiliary
  deriving BEq, Hashable

/-- A scope belongs to one snapshot traversal position, never to a union of locals. -/
structure ExpressionOwner where
  label : String
  lctx : LocalContext
  scope : Nat

structure CheckedTransition where
  state : GoalState
  hasSorry : Bool
  hasUnsafe : Bool
  auxiliaryResidue : Array String := #[]
  executableUnresolved : List MVarId := []

private structure Scan where
  nextScope : Nat := 0
  mvars : HashSet (MVarId × ValidationPurpose) := {}
  constants : HashSet (Name × ValidationPurpose) := {}
  fvars : HashSet (Nat × FVarId × ValidationPurpose) := {}
  activeLocals : HashSet (Nat × FVarId × ValidationPurpose) := {}
  activeMVars : HashSet (MVarId × ValidationPurpose) := {}
  activeLevels : HashSet LMVarId := {}
  levels : HashSet LMVarId := {}
  unresolved : Array MVarId := #[]
  residue : Array String := #[]
  hasSorry : Bool := false
  hasUnsafe : Bool := false

private structure ScanContext where
  trusted : Environment
  state : GoalState

private abbrev ScanM := ReaderT ScanContext (StateT Scan (ExceptT String CoreM))

private def poll : ScanM Unit := Core.checkSystem "scope-aware-validation"

private def owner (label : String) (lctx : LocalContext) : ScanM ExpressionOwner := do
  let scope := (← get).nextScope
  modify fun s => { s with nextScope := scope + 1 }
  return { label, lctx, scope }

private def problem (purpose : ValidationPurpose) (owner : ExpressionOwner)
    (path message : String) : ScanM α :=
  throwThe String s!"{if purpose == .execution then "execution" else "auxiliary"} owner={owner.label} path={path.take 512}: {message}"

private def residue (o : ExpressionOwner) (path message : String) : ScanM Unit := do
  -- Evidence is bounded independently of the number of discarded elaboration records.
  if (← get).residue.size < 32 then
    modify fun s => { s with residue := s.residue.push s!"owner={o.label} path={path.take 256}: {message}" }

private partial def inspectLevel (o : ExpressionOwner) (path : String) (level : Level) : ScanM Unit := do
  poll
  match level with
  | .succ a => inspectLevel o path a
  | .max a b | .imax a b => inspectLevel o path a; inspectLevel o path b
  | .mvar id =>
    if (← get).activeLevels.contains id then problem .execution o path s!"Cyclic universe assignment {id.name}"
    unless (← get).levels.contains id do
      let mctx := (← read).state.mctx
      unless mctx.lDepth.contains id do problem .execution o path s!"Missing universe declaration {id.name}"
      modify fun s => { s with activeLevels := s.activeLevels.insert id }
      if let some value := mctx.lAssignment.find? id then inspectLevel o path value
      modify fun s => { s with levels := s.levels.insert id, activeLevels := s.activeLevels.erase id }
  | _ => pure ()

mutual
  private partial def inspectExpr (purpose : ValidationPurpose) (o : ExpressionOwner)
      (path : String) (depth : Nat) (expr : Expr) : ScanM Unit := do
    poll
    let env := (← read).state.env
    match expr with
    | .bvar index =>
      if purpose == .execution && index >= depth then problem purpose o path s!"Loose bound variable {index} at depth {depth}"
    | .mvar id =>
      inspectMVar purpose id (path ++ "/metavariable")
      if purpose == .execution then checkUse o path depth id
    | .fvar id =>
      -- Membership is checked before memoization, including at narrower context prefixes.
      match o.lctx.find? id with
      | none =>
        if purpose == .execution then problem purpose o path s!"Missing local declaration {id.name}"
        else residue o path s!"Missing local declaration {id.name}"
      | some decl =>
        let key := (o.scope, id, purpose)
        if (← get).activeLocals.contains key then problem purpose o path s!"Cyclic local declaration {id.name}"
        unless (← get).fvars.contains key do
          modify fun s => { s with activeLocals := s.activeLocals.insert key }
          inspectExpr purpose o (path ++ "/local-type") 0 decl.type
          if let some value := decl.value? then inspectExpr purpose o (path ++ "/local-value") 0 value
          modify fun s => { s with fvars := s.fvars.insert key, activeLocals := s.activeLocals.erase key }
    | .const name levels =>
      if name == ``sorryAx then modify fun s => { s with hasSorry := true }
      if purpose == .execution then levels.forM (inspectLevel o (path ++ "/universe"))
      inspectConstant purpose o path name
    | .sort level => if purpose == .execution then inspectLevel o path level
    | .app fn arg =>
      inspectExpr purpose o (path ++ "/function") depth fn
      inspectExpr purpose o (path ++ "/argument") depth arg
    | .lam _ type body _ | .forallE _ type body _ =>
      inspectExpr purpose o (path ++ "/binder-type") depth type
      inspectExpr purpose o (path ++ "/binder-body") (depth + 1) body
    | .letE _ type value body _ =>
      inspectExpr purpose o (path ++ "/let-type") depth type
      inspectExpr purpose o (path ++ "/let-value") depth value
      inspectExpr purpose o (path ++ "/let-body") (depth + 1) body
    | .mdata _ body => inspectExpr purpose o path depth body
    | .proj name index body =>
      let some field := (getStructureFields env name).get? index | problem purpose o path s!"Missing projection field {name}.{index}"
      let some projector := getProjFnForField? env name field | problem purpose o path s!"Missing projection dependency {name}.{field}"
      inspectConstant purpose o path projector
      inspectExpr purpose o (path ++ "/projection") depth body
    | .lit _ => pure ()

  private partial def inspectConstant (purpose : ValidationPurpose) (o : ExpressionOwner)
      (path : String) (name : Name) : ScanM Unit := do
    poll
    unless (← get).constants.contains (name, purpose) do
      modify fun s => { s with constants := s.constants.insert (name, purpose) }
      let ctx ← read
      let some info := ctx.state.env.find? name | problem purpose o path s!"Missing proof dependency {name}"
      if info.isUnsafe then modify fun s => { s with hasUnsafe := true }
      unless ctx.trusted.contains name do
        if info.type.hasMVar || info.value?.any Expr.hasMVar then
          problem .execution o path s!"Unresolved metavariable in environment declaration {name}"
        let closed ← owner s!"declaration {name}" {}
        -- Environment declarations must always be closed, including unused additions.
        inspectExpr .execution closed (path ++ "/declaration-type") 0 info.type
        if let some value := info.value? then inspectExpr .execution closed (path ++ "/declaration-value") 0 value

  private partial def inspectContext (purpose : ValidationPurpose) (o : ExpressionOwner)
      (path : String) (instances : LocalInstances := #[]) : ScanM Unit := do
    let mut priorContext : LocalContext := {}
    for decl in o.lctx do
      let prior ← owner s!"{o.label}/local {decl.fvarId.name}" priorContext
      inspectExpr purpose prior (path ++ "/local-type") 0 decl.type
      if let some value := decl.value? then inspectExpr purpose prior (path ++ "/local-value") 0 value
      priorContext := priorContext.addDecl decl
    for localInstance in instances do inspectExpr purpose o (path ++ "/local-instance") 0 localInstance.fvar

  private partial def inspectMVar (purpose : ValidationPurpose) (id : MVarId) (path : String) : ScanM Unit := do
    poll
    let key := (id, purpose)
    let mctx := (← read).state.mctx
    let some decl := mctx.findDecl? id | do
      let unknown ← owner s!"metavariable {id.name}" {}
      problem purpose unknown path s!"Missing metavariable declaration {id.name}"
    if (← get).activeMVars.contains key then
      let o ← owner s!"metavariable {id.name}" decl.lctx
      problem purpose o path s!"Cyclic metavariable assignment {id.name}"
    unless (← get).mvars.contains key do
      modify fun s => { s with activeMVars := s.activeMVars.insert key }
      let o ← owner s!"metavariable {id.name}" decl.lctx
      inspectContext purpose o path decl.localInstances
      inspectExpr purpose o (path ++ "/type") 0 decl.type
      if let some value := mctx.eAssignment.find? id then
        inspectExpr purpose o (path ++ "/assignment") 0 value
      else if let some delayed := mctx.dAssignment.find? id then
        let some pending := mctx.findDecl? delayed.mvarIdPending |
          problem purpose o path "Missing delayed assignment target"
        let pendingOwner ← owner s!"delayed target {delayed.mvarIdPending.name}" pending.lctx
        let mut seen : HashSet FVarId := {}
        for value in delayed.fvars do
          if purpose == .execution then
            unless value.isFVar && !seen.contains value.fvarId! do
              problem purpose o path "Invalid delayed abstraction variable"
            seen := seen.insert value.fvarId!
          inspectExpr purpose pendingOwner (path ++ "/delayed-abstraction") 0 value
        inspectMVar purpose delayed.mvarIdPending (path ++ "/delayed-target")
        if purpose == .execution then checkUse o path 0 id
      else if purpose == .execution then
        modify fun s => { s with unresolved := s.unresolved.push id }
      modify fun s => { s with mvars := s.mvars.insert key, activeMVars := s.activeMVars.erase key }

  /-- Check the scope at a use site as well as at the stored assignment's owner. -/
  private partial def checkUse (o : ExpressionOwner) (path : String) (depth : Nat) (id : MVarId) : ScanM Unit := do
    let mctx := (← read).state.mctx
    if let some value := mctx.eAssignment.find? id then
      let (expanded, _) := instantiateMVarsCore mctx value
      -- The owned traversal has already checked cycles before expansion.
      for localDecl in (Lean.collectFVars {} expanded).fvarIds do
        unless (o.lctx.find? localDecl).isSome do problem .execution o path s!"Escaping local declaration {localDecl.name} from {id.name}"
      -- An unresolved dependency retains its whole assignment scope at the use site.
      for pending in (expanded.collectMVars {}).result do checkUse o path depth pending
    else if let some delayed := mctx.dAssignment.find? id then
      let some pending := mctx.findDecl? delayed.mvarIdPending | problem .execution o path "Missing delayed assignment target"
      let (value, _) := instantiateMVarsCore mctx (.mvar delayed.mvarIdPending)
      if !value.hasExprMVar then
        let abstracted := value.abstract delayed.fvars
        for localDecl in (Lean.collectFVars {} abstracted).fvarIds do
          unless (o.lctx.find? localDecl).isSome do problem .execution o path s!"Escaping delayed local declaration {localDecl.name}"
        if abstracted.hasLooseBVars && abstracted.looseBVarRange > depth + delayed.fvars.size then
          problem .execution o path "Loose delayed abstraction variable"
      else
        for localDecl in pending.lctx do
          unless delayed.fvars.contains (.fvar localDecl.fvarId) || (o.lctx.find? localDecl.fvarId).isSome do
            problem .execution o path s!"Escaping pending local declaration {localDecl.fvarId.name}"
    else if let some decl := mctx.findDecl? id then
      for localDecl in decl.lctx do
        unless (o.lctx.find? localDecl.fvarId).isSome do
          problem .execution o path s!"Escaping unassigned local declaration {localDecl.fvarId.name}"
end

/-- Derived caches are rebuildable; executable work and metavariable records are preserved. -/
def GoalState.withoutDerivedCaches (state : GoalState) : GoalState :=
  { state with savedState := { state.savedState with term := { state.savedState.term with
    meta := { state.savedState.term.meta with
      core := { state.savedState.term.meta.core with cache := {} },
      meta := { state.metaState with cache := {} } } } } }

private def scanExecution (requested : List MVarId) : ScanM Unit := do
  let state := (← read).state
  let roots := state.publishedObligations ++ state.goals ++ requested ++
    state.parentMVar?.toList ++ (state.convMVar?.map (fun (rhs, goal, dormant) => rhs :: goal :: dormant) |>.getD [])
  if state.root.name != .anonymous then inspectMVar .execution state.root "root"
  for id in roots.eraseDups do inspectMVar .execution id "retained obligation"
  if let some decl := state.mctx.findDecl? state.root then
    let o ← owner "original root statement" decl.lctx
    inspectExpr .execution o "root type" 0 state.rootType
  if let some (id, expression) := state.calcPrevRhs? then
    inspectMVar .execution id "calculation goal"
    let some decl := state.mctx.findDecl? id | throwThe String "execution owner=calculation path=calculation RHS: Missing calculation owner"
    let o ← owner "calculation RHS" decl.lctx
    inspectExpr .execution o "calculation RHS" 0 expression
  let proofUnresolved := (← get).unresolved
  let termState := state.savedState.term.elab
  for id in termState.pendingMVars do inspectMVar .execution id "pending elaboration"
  for (id, synthetic) in termState.syntheticMVars.toList do
    inspectMVar .execution id "synthetic elaboration"
    if let .coe _ type expression fn? := synthetic.kind then
      let some decl := state.mctx.findDecl? id | throwThe String "execution owner=coercion path=synthetic work: Missing coercion owner"
      let o ← owner s!"synthetic coercion {id.name}" decl.lctx
      inspectExpr .execution o "coercion type" 0 type
      inspectExpr .execution o "coercion expression" 0 expression
      if let some fn := fn? then inspectExpr .execution o "coercion function" 0 fn
  for work in termState.letRecsToLift do
    let o ← owner s!"let-rec {work.declName}" work.lctx
    inspectContext .execution o "let-rec context" work.localInstances
    inspectExpr .execution o "let-rec type" 0 work.type
    inspectExpr .execution o "let-rec value" 0 work.val
    inspectExpr .execution o "let-rec local" 0 (.fvar work.fvarId)
    inspectMVar .execution work.mvarId "let-rec obligation"
  for constraint in state.metaState.postponed do
    let lctx := constraint.ctx?.map (·.lctx) |>.getD {}
    let o ← owner "postponed universe constraint" lctx
    inspectLevel o "universe lhs" constraint.lhs
    inspectLevel o "universe rhs" constraint.rhs
    if let some ctx := constraint.ctx? then
      inspectContext .execution o "postponed context" ctx.localInstances
      inspectExpr .execution o "postponed lhs" 0 ctx.lhs
      inspectExpr .execution o "postponed rhs" 0 ctx.rhs

  modify fun s => { s with unresolved := proofUnresolved }

private def auditAuxiliary : ScanM Unit := do
  let ctx ← read
  -- Stored syntax remains auditable even when a record has no execution path.
  for (id, _) in ctx.state.mctx.decls.toList do inspectMVar .auxiliary id "retained record audit"
  for (id, _) in ctx.state.mctx.eAssignment.toList do
    unless ctx.state.mctx.decls.contains id do
      let o ← owner s!"ordinary assignment {id.name}" {}
      problem .auxiliary o "assignment audit" "Missing assignment owner"
  for (id, _) in ctx.state.mctx.dAssignment.toList do
    unless ctx.state.mctx.decls.contains id do
      let o ← owner s!"delayed assignment {id.name}" {}
      problem .auxiliary o "assignment audit" "Missing delayed assignment owner"
  let additions := ctx.state.env.constants.foldStage2 (fun acc name _ =>
    if ctx.trusted.contains name then acc else name :: acc) []
  let closed ← owner "retained environment additions" {}
  for name in additions do inspectConstant .auxiliary closed "environment audit" name
  for info in ctx.state.savedState.term.elab.mvarErrorInfos do
    if let .implicitArg expression := info.kind then
      let lctx := (ctx.state.mctx.findDecl? info.mvarId).map (·.lctx) |>.getD {}
      let o ← owner s!"diagnostic {info.mvarId.name}" lctx
      inspectExpr .auxiliary o "implicit argument diagnostic" 0 expression
  for (expression, _) in ctx.state.metaState.diag.synthPendingFailures.toList do
    let o ← owner "synthesis diagnostic" {}
    inspectExpr .auxiliary o "synthesis diagnostic" 0 expression

private def runValidation (state : GoalState) (requested : List MVarId) : CoreM (Except String CheckedTransition) := do
  withCommandPhase "validate" do
    let action : ScanM Unit := do
      scanExecution requested
      auditAuxiliary
    let result ← ((action.run { trusted := state.trustedEnv, state }).run {}).run
    return result.map fun (_, evidence) => {
      state := state.withoutDerivedCaches,
      hasSorry := evidence.hasSorry, hasUnsafe := evidence.hasUnsafe,
      auxiliaryResidue := evidence.residue, executableUnresolved := evidence.unresolved.toList.eraseDups }

/-- Validate a retained state before an operation makes additional records observable. -/
def validateSnapshot (state : GoalState) (requested : List MVarId := []) : CoreM (Except String CheckedTransition) :=
  runValidation state requested

/-- Strict execution roots and an independent audit share the request's finite budget. -/
def validateTransition (before after : GoalState) (selected : MVarId) : CoreM (Except String CheckedTransition) := do
  if before.root != after.root || !Expr.equal before.rootType after.rootType || before.rootLevels != after.rootLevels then
    return .error "execution owner=original root path=root: root identity, statement, or universe parameters changed"
  let requested := (selected :: before.goals ++ before.publishedObligations).eraseDups
  let state := { after with trustedEnv := before.trustedEnv, publishedObligations := (after.publishedObligations ++ requested ++ after.goals).eraseDups }
  let checked ← runValidation state requested
  match checked with
  | .error message => return .error message
  | .ok evidence =>
    if let some prior := before.mctx.findDecl? before.root then
      let some current := after.mctx.findDecl? after.root |
        return .error "execution owner=original root path=root: missing declaration"
      let ids (lctx : LocalContext) := lctx.foldl (init := #[]) fun acc decl => acc.push decl.fvarId
      unless ids prior.lctx == ids current.lctx do
        return .error "execution owner=original root path=root: local context identities changed"
      for decl in prior.lctx do
        let some next := current.lctx.find? decl.fvarId |
          return .error "execution owner=original root path=root: missing local declaration"
        let inst (value : Expr) := (instantiateMVarsCore state.mctx value).1
        unless Expr.equal (inst decl.type) (inst next.type) && decl.value?.map inst == next.value?.map inst do
          return .error "execution owner=original root path=root: local declaration type or value changed"
    -- Auxiliary and resumable metadata roots do not create scratch proof goals.
    let dormant := before.goals.filter (· != selected)
    let conversion := after.convMVar?.map (fun (rhs, goal, siblings) => rhs :: goal :: siblings) |>.getD []
    let conversion := after.goals.foldl (init := conversion) fun acc goal =>
      match after.mctx.findDecl? goal with
      | some decl =>
        if (isLHSGoal? decl.type).isSome then
          let (rhs, _) := instantiateMVarsCore after.mctx decl.type.consumeMData.appArg!
          acc ++ (rhs.collectMVars {}).result.toList
        else acc
      | none => acc
    let extra := evidence.executableUnresolved.filter fun id =>
      !after.goals.contains id && !dormant.contains id && !conversion.contains id
    let state := { evidence.state with
      publishedObligations := (state.publishedObligations ++ extra).eraseDups,
      savedState := { evidence.state.savedState with tactic := { goals := after.goals ++ extra } } }
    return .ok { evidence with state }

builtin_initialize validationExceptionId : InternalExceptionId ←
  registerInternalExceptionId `pantographValidationFailure

/-- Abort publication through the shared transaction rather than returning a successful handler value. -/
def requireValidation (action : CoreM (Except String CheckedTransition)) : CoreM CheckedTransition := do
  match ← action with
  | .ok checked => return checked
  | .error message =>
    throw <| .internal validationExceptionId <| ({} : KVMap).setString `desc (message.take 2048)

/-- Native operation exports share the transition boundary used by REPL publication. -/
def validateOperation [Monad m] [MonadLiftT CoreM m] (before : GoalState) (selected : MVarId)
    (action : m TacticResult) : m TacticResult := do
  match ← action with
  | .success after => return .success (← requireValidation (validateTransition before after selected)).state
  | other => return other

end Pantograph
