import Test.Common
import Test.ContractFixtures
import Pantograph.Validation
import Pantograph.Certify
import Repl

namespace Pantograph.Test.ScopeValidation
open Lean

private def withMCtx (state : GoalState) (mctx : MetavarContext) : GoalState :=
  { state with savedState := { state.savedState with term := { state.savedState.term with
    meta := { state.savedState.term.meta with meta := { state.metaState with mctx } } } } }

private def withTerm (state : GoalState) (term : Elab.Term.SavedState) (goals : List MVarId) : GoalState :=
  { state with savedState := { term, tactic := { goals } } }

private def rejects (result : Except String CheckedTransition) : Bool := result.toOption.isNone

private def tests : Elab.TermElabM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let .ok base ← goalStartExpr "True" #[] | throwError "start failed"
  let .success raw ← base.tryTactic base.root "contract_inert_residue" | throwError "residue tactic failed"
  let checked ← validateTransition base raw base.root
  let some good := checked.toOption | throwError "residue rejected"
  tests := tests ++ LSpec.test "inert orphan syntax is retained and reported without new proof goals"
    (!good.auxiliaryResidue.isEmpty && good.state.goals.isEmpty &&
      good.state.mctx.eAssignment.toList.length == raw.mctx.eAssignment.toList.length &&
      !good.hasSorry && !good.hasUnsafe)
  tests := tests ++ LSpec.test "the original completed root has a kernel receipt"
    ((← certifyRoot good.state 200000).status == "certified")
  let some (scratch, _) := raw.mctx.eAssignment.toList.find? (fun (id, value) =>
      id != raw.root && value.isFVar) | throwError "no orphan record"
  let scratchExpr := raw.mctx.eAssignment.find? scratch |>.getD (mkNatLit 0)
  let promoted := withMCtx good.state { good.state.mctx with
    eAssignment := good.state.mctx.eAssignment.insert good.state.root (.mvar scratch) }
  tests := tests ++ LSpec.test "previously inert data is checked strictly when the root reaches it"
    (rejects (← validateTransition good.state promoted good.state.root))
  tests := tests ++ LSpec.test "an unpublished record is checked strictly when inspection requests it"
    (rejects (← validateSnapshot good.state [scratch]))
  let hazard := mkApp2 (mkConst ``And.intro) scratchExpr (mkApp (mkConst ``sorryAx [.zero]) (mkConst ``True))
  let poisoned := withMCtx raw { raw.mctx with eAssignment := raw.mctx.eAssignment.insert scratch hazard }
  tests := tests ++ LSpec.test "missing auxiliary ownership does not skip an independent admission branch"
    ((← validateTransition base poisoned base.root).toOption.any (·.hasSorry))
  let poisoned := withMCtx raw { raw.mctx with eAssignment := raw.mctx.eAssignment.insert scratch (mkApp scratchExpr (mkConst `ContractFixtures.unusedUnsafe)) }
  tests := tests ++ LSpec.test "missing auxiliary ownership does not skip an independent unsafe branch"
    ((← validateTransition base poisoned base.root).toOption.any (·.hasUnsafe))
  base.restoreElabM
  let hole ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let orphan := withTerm base (← Elab.Term.saveState) []
  let orphan := withMCtx orphan { orphan.mctx with eAssignment := orphan.mctx.eAssignment.insert base.root (mkConst ``True.intro) }
  let unneeded ← validateTransition base orphan base.root
  tests := tests ++ LSpec.test "an unassigned scratch record is not advertised as a proof obligation"
    (unneeded.toOption.any (·.state.goals.isEmpty))
  let live := withMCtx orphan { orphan.mctx with eAssignment := orphan.mctx.eAssignment.insert base.root hole }
  tests := tests ++ LSpec.test "a reachable hidden hole survives assignment of its parent"
    ((← validateTransition base live base.root).toOption.any fun result => result.state.goals == [hole.mvarId!])
  tests := tests ++ LSpec.test "an incomplete root never certifies"
    ((← certifyRoot live 200000).status != "certified")
  let dangling := withMCtx base { base.mctx with eAssignment := base.mctx.eAssignment.insert base.root (.fvar ⟨`Scope.missing⟩) }
  tests := tests ++ LSpec.test "a root assignment cannot use a dangling free variable"
    (rejects (← validateTransition base dangling base.root))
  let lctx := (base.mctx.findDecl? base.root).get!.lctx.mkLetDecl ⟨`Scope.badLet⟩ `unused
    (mkConst ``True) (.fvar ⟨`Scope.missing⟩)
  let decl := { (base.mctx.findDecl? base.root).get! with lctx }
  let invalidLet := withMCtx base { base.mctx with decls := base.mctx.decls.insert base.root decl }
  tests := tests ++ LSpec.test "unused live local values still require valid ownership"
    (rejects (← validateTransition base invalidLet base.root))
  let loose := withMCtx base { base.mctx with eAssignment := base.mctx.eAssignment.insert base.root (.bvar 0) }
  tests := tests ++ LSpec.test "loose bound variables reject"
    (rejects (← validateTransition base loose base.root))
  let .ok function ← goalStartExpr "True → True" #[] | throwError "function start failed"
  let bound := withMCtx function { function.mctx with eAssignment := function.mctx.eAssignment.insert function.root (.lam `proof (mkConst ``True) (.bvar 0) .default) }
  tests := tests ++ LSpec.test "bound variables under their lambda are accepted"
    ((← validateTransition function bound function.root).toOption.isSome)
  let missing : MVarId := ⟨`Scope.missingMVar⟩
  let invalid := withMCtx base { base.mctx with eAssignment := base.mctx.eAssignment.insert base.root (.mvar missing) }
  tests := tests ++ LSpec.test "missing executable metavariable declarations reject"
    (rejects (← validateTransition base invalid base.root))
  let invalid := withMCtx base { base.mctx with dAssignment := base.mctx.dAssignment.insert base.root { fvars := #[], mvarIdPending := missing } }
  tests := tests ++ LSpec.test "missing delayed targets reject"
    (rejects (← validateTransition base invalid base.root))
  let invalid := withMCtx base { base.mctx with dAssignment := base.mctx.dAssignment.insert base.root { fvars := #[], mvarIdPending := base.root } }
  tests := tests ++ LSpec.test "delayed assignment cycles reject"
    (rejects (← validateTransition base invalid base.root))
  let pending := { raw with savedState := { raw.savedState with term := { raw.savedState.term with
    «elab» := { raw.savedState.term.elab with pendingMVars := [scratch] } } } }
  tests := tests ++ LSpec.test "pending work cannot be classified as inert residue"
    (rejects (← validateTransition base pending base.root))
  let synthetic := { raw with savedState := { raw.savedState with term := { raw.savedState.term with
    «elab» := { raw.savedState.term.elab with syntheticMVars := raw.savedState.term.elab.syntheticMVars.insert scratch { stx := .missing, kind := .coe none (mkConst ``True) scratchExpr none } } } } }
  tests := tests ++ LSpec.test "synthetic coercion expressions keep their owner"
    (rejects (← validateTransition base synthetic base.root))
  let postponed := { raw with savedState := { raw.savedState with term := { raw.savedState.term with
    meta := { raw.savedState.term.meta with meta := { raw.metaState with postponed := ({} : PersistentArray Meta.PostponedEntry).push {
      ref := .missing, lhs := .zero, rhs := .zero,
      ctx? := some { lhs := scratchExpr, rhs := mkConst ``True, lctx := {}, localInstances := #[] } } } } } } }
  tests := tests ++ LSpec.test "postponed constraints keep strict expression owners"
    (rejects (← validateTransition base postponed base.root))
  let withCache := { raw with savedState := { raw.savedState with term := { raw.savedState.term with
    meta := { raw.savedState.term.meta with core := { raw.savedState.term.meta.core with
      cache := { instLevelType := ({} : Core.InstantiateLevelCache).insert `Scope.cached ([], scratchExpr) } } } } } }
  let normalized ← validateTransition base withCache base.root
  tests := tests ++ LSpec.test "derived cache references are removed without deleting metavariable records"
    (normalized.toOption.any fun result =>
      (result.state.savedState.term.meta.core.cache.instLevelType.find? `Scope.cached).isNone &&
      result.state.mctx.decls.contains scratch)
  -- A repeated local identity must not borrow validation from an unrelated context.
  base.restoreElabM
  let (scopedState, fvar) ← Meta.withLocalDeclD `shared (mkConst ``True) fun value => do
    return (← GoalState.create (mkConst ``True), value)
  let second ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let before := withTerm scopedState (← Elab.Term.saveState) [scopedState.root, second.mvarId!]
  let after := withMCtx before { before.mctx with eAssignment := before.mctx.eAssignment.insert scopedState.root fvar |>.insert second.mvarId! fvar }
  tests := tests ++ LSpec.test "visited locals cannot suppress a membership check in another owner"
    (rejects (← validateTransition before after scopedState.root))
  base.restoreElabM
  let level ← Meta.mkFreshLevelMVar
  let universeState ← GoalState.create (.sort level)
  let universeState := withMCtx universeState { universeState.mctx with eAssignment := universeState.mctx.eAssignment.insert universeState.root (.sort .zero) }
  let universeState := { universeState with savedState := { universeState.savedState with tactic := { goals := [] } } }
  tests := tests ++ LSpec.test "unresolved universe obligations never yield a certificate"
    ((← certifyRoot universeState 200000).status != "certified")
  let invalid := withMCtx universeState { universeState.mctx with lAssignment := universeState.mctx.lAssignment.insert level.mvarId! (.succ level) }
  tests := tests ++ LSpec.test "cyclic universe assignments reject before instantiation"
    (rejects (← validateSnapshot invalid))
  tests := tests ++ LSpec.test "the original root statement cannot be replaced"
    (rejects (← validateTransition base { raw with rootType := mkConst ``False } base.root))
  let calculation := { raw with calcPrevRhs? := some (raw.root, scratchExpr) }
  tests := tests ++ LSpec.test "saved calculation expressions require their recorded owner"
    (rejects (← validateTransition base calculation base.root))
  let conversion := { raw with convMVar? := some (missing, raw.root, []) }
  tests := tests ++ LSpec.test "conversion RHS and dormant identities are strict roots"
    (rejects (← validateTransition base conversion base.root))
  let work : Elab.Term.LetRecToLift := {
    ref := .missing, fvarId := ⟨`Scope.letRec⟩, attrs := #[], shortDeclName := `f,
    declName := `Scope.f, lctx := {}, localInstances := #[], type := mkConst ``True,
    val := scratchExpr, mvarId := scratch, termination := .none }
  let pendingRec := { raw with savedState := { raw.savedState with term := { raw.savedState.term with
    «elab» := { raw.savedState.term.elab with letRecsToLift := [work] } } } }
  tests := tests ++ LSpec.test "let-rec work cannot hide an invalid saved expression"
    (rejects (← validateTransition base pendingRec base.root))
  base.restoreElabM
  let admission ← Meta.mkSorry (mkConst ``True) false
  let retained ← Meta.withLetDecl `unused (mkConst ``True) admission fun _ => GoalState.create (mkConst ``True)
  let finished := withMCtx retained { retained.mctx with eAssignment := retained.mctx.eAssignment.insert retained.root (mkConst ``True.intro) }
  let finished := { finished with savedState := { finished.savedState with tactic := { goals := [] } } }
  tests := tests ++ LSpec.test "unused retained local admissions remain visible to validation"
    ((← validateTransition retained finished retained.root).toOption.any (·.hasSorry))
  tests := tests ++ LSpec.test "certification cannot erase an unused local admission through abstraction"
    ((← certifyRoot finished 200000).status == "rejected")
  base.restoreElabM
  let fn ← Meta.mkFreshExprSyntheticOpaqueMVar (← mkArrow (mkConst ``True) (mkConst ``True))
  let (pending, argument) ← Meta.withLocalDeclD `argument (mkConst ``True) fun argument => do
    let pending ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
    pending.mvarId!.assign argument
    return (pending, argument)
  assignDelayedMVar fn.mvarId! #[argument] pending.mvarId!
  base.root.assign (mkApp fn (mkConst ``True.intro))
  let delayed := withTerm base (← Elab.Term.saveState) []
  tests := tests ++ LSpec.test "delayed abstraction uses the pending owner's context"
    ((← validateTransition base delayed base.root).toOption.isSome)
  tests := tests ++ LSpec.test "the delayed substitution produces a certified root"
    ((← certifyRoot delayed 200000).status == "certified")
  let escaping := withMCtx delayed { delayed.mctx with dAssignment := delayed.mctx.dAssignment.insert fn.mvarId! { fvars := #[], mvarIdPending := pending.mvarId! } }
  tests := tests ++ LSpec.test "delayed substitution cannot borrow an unabstracted local"
    (rejects (← validateTransition base escaping base.root))
  base.restoreElabM
  let (wrapper, dependency) ← Meta.withLocalDeclD `temporary (mkConst ``True) fun _ => do
    let dependency ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
    let wrapper ← Meta.mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
    wrapper.mvarId!.assign dependency
    return (wrapper, dependency)
  base.root.assign wrapper
  let escapingPending := withTerm base (← Elab.Term.saveState) [dependency.mvarId!]
  tests := tests ++ LSpec.test "an assigned wrapper cannot conceal an escaping unresolved scope"
    (rejects (← validateTransition base escapingPending base.root))
  base.restoreElabM
  let assignedUniverse ← Meta.mkFreshLevelMVar
  assignLevelMVar assignedUniverse.mvarId! (.param `u)
  let (nativeRoot, frontendRoot) ← Meta.withLocalDeclD `α (.sort assignedUniverse) fun alpha =>
    Meta.withLocalDeclD `a alpha fun value => do
      let nativeRoot ← GoalState.create alpha
      nativeRoot.root.assign value
      let frontendRoot ← GoalState.createFromMVars [] nativeRoot.root
      let nativeRoot := withTerm nativeRoot (← Elab.Term.saveState) []
      return (nativeRoot, frontendRoot)
  tests := tests ++ LSpec.test "shared root constructors retain universes that occur only in local types"
    (nativeRoot.rootLevels == [`u] && frontendRoot.rootLevels == [`u])
  tests := tests ++ LSpec.test "native and frontend roots certify with their retained universe owners"
    ((← certifyRoot nativeRoot 200000).status == "certified" &&
      (← certifyRoot frontendRoot 200000).status == "certified")
  return tests

private def transactionTests : Repl.MainM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let command : Protocol.Command := { cmd := "stat", payload := Json.mkObj [] }
  let rootResponse ← Repl.execute { cmd := "goal.start", payload := Json.mkObj [("expr", "True")] }
  let id := rootResponse.getObjValAs? Nat "stateId" |>.toOption |>.getD 99999
  let entry ← get
  let some root := entry.goalStates.find? id | throwError "no root"
  let mut expression := mkConst ``True.intro
  for _ in [:16] do expression := .app expression expression
  for phase in ["execution closure", "auxiliary audit"] do
    let scratch : MVarId := ⟨`Scope.resourceScratch⟩
    let decl := (root.mctx.findDecl? root.root).get!
    let mctx := { root.mctx with decls := root.mctx.decls.insert scratch decl }
    let mctx := { mctx with eAssignment := mctx.eAssignment.insert root.root (if phase == "execution closure" then expression else mkConst ``True.intro) |>.insert scratch expression }
    let state := withMCtx root mctx
    let exhausted ← Repl.runTransaction command do
      discard <| requireValidation (validateSnapshot state)
      return Json.null
    let resource := exhausted.response.getObjVal? "resource" |>.toOption |>.getD Json.null
    tests := tests ++ LSpec.test s!"resource exhaustion in {phase} preserves transaction framing"
      (!exhausted.fatal && (exhausted.response.getObjValAs? String "error").toOption == some "resource" &&
        (resource.getObjValAs? String "phase").toOption == some "validate" &&
        (exhausted.response.getObjValAs? String "recovery").toOption == some "command-rolled-back" &&
        (← get).nextId == entry.nextId && (← get).goalStates.size == entry.goalStates.size)
  let fatal ← Repl.runTransaction command do
    modify fun state => { state with
      goalStates := {}, nextId := 99999,
      options := { state.options with printExprAST := true } }
    discard <| Pantograph.Environment.addDecl {
      name := "Scope.temporary", type := "True", value := "True.intro", isTheorem := false }
    logInfo "staged validation failure"
    let corrupted := withMCtx root { root.mctx with eAssignment := root.mctx.eAssignment.insert root.root (.fvar ⟨`Scope.missing⟩) }
    discard <| requireValidation (validateSnapshot corrupted)
    return Json.null
  tests := tests ++ LSpec.test "validation abort discards allocations, options, declarations and messages"
    (fatal.fatal && (fatal.response.getObjValAs? String "error").toOption == some "validation" &&
      (fatal.response.getObjVal? "nextStateId").toOption.isNone &&
      (← get).goalStates.contains id && (← get).nextId == entry.nextId && !(← get).options.printExprAST &&
      !(← getEnv).contains `Scope.temporary && (← getThe Core.State).messages.toArray.isEmpty)
  let refused ← Repl.executeCommand command
  tests := tests ++ LSpec.test "validation integrity failure refuses further commands" refused.fatal
  return tests

private def requestedRecordTests (operation : String) : Repl.MainM LSpec.TestSeq := do
  let root ← Repl.execute { cmd := "goal.start", payload := Json.mkObj [("expr", "True")] }
  let id := root.getObjValAs? Nat "stateId" |>.toOption |>.getD 99999
  let done ← Repl.execute { cmd := "goal.tactic", payload := Json.mkObj [("stateId", toJson id), ("tactic", "contract_inert_residue")] }
  let next := done.getObjValAs? Nat "nextStateId" |>.toOption |>.getD 99999
  let entry ← get
  let some snapshot := entry.goalStates.find? next | throwError "missing retained result"
  let some (scratch, _) := snapshot.mctx.eAssignment.toList.find? (fun (_, value) => value.isFVar) |
    throwError "missing inert record"
  let payload := if operation == "goal.inspect" then
      Json.mkObj [("stateId", toJson next), ("goals", toJson [scratch.name.toString])]
    else Json.mkObj [("target", toJson next), ("goals", toJson [scratch.name.toString])]
  let result ← Repl.executeCommand { cmd := operation, payload }
  return LSpec.test s!"{operation} validates a newly requested inert record before publication"
    (result.fatal && (result.response.getObjValAs? String "error").toOption == some "validation" &&
      (result.response.getObjVal? "nextStateId").toOption.isNone &&
      (← get).nextId == entry.nextId && (← get).goalStates.size == entry.goalStates.size)

def suite (_ : Environment) : List (String × IO LSpec.TestSeq) := [
  ("Ownership and auxiliary audit", do
    let env ← importModules #[{ module := `Test.ContractFixtures }] {} (trustLevel := 1)
    runTermElabMSeq env tests),
  ("Validation transaction and resource budgets", do
    let env ← importModules #[{ module := `Test.ContractFixtures }] {} (trustLevel := 1)
    runCoreMSeq env (transactionTests.run { imports := ["Test.ContractFixtures"] } |>.run' {}) #["maxHeartbeats=100"]),
  ("Inspection publication", do
    let env ← importModules #[{ module := `Test.ContractFixtures }] {} (trustLevel := 1)
    runCoreMSeq env ((requestedRecordTests "goal.inspect").run { imports := ["Test.ContractFixtures"] } |>.run' {})),
  ("Continuation publication", do
    let env ← importModules #[{ module := `Test.ContractFixtures }] {} (trustLevel := 1)
    runCoreMSeq env ((requestedRecordTests "goal.continue").run { imports := ["Test.ContractFixtures"] } |>.run' {}))
]

end Pantograph.Test.ScopeValidation
