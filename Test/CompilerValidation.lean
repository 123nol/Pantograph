import Test.Common
import Pantograph.DeclarationAudit
import Pantograph.Validation
import Pantograph.Certify

/-! Compiler-producing tactics and the representation-aware audit.

`unfold Nat.pow` generates the match splitter for `Nat.pow.match_1`, which is
compiled on demand; the code generator then stores its stage entries
(`_private.0.Nat.pow.match_1.splitter._cstage1`, `…splitter._cstage2`,
`…splitter._rarg._cstage2`) in the retained environment. -/

namespace Pantograph.Test.CompilerValidation
open Lean

private def withEnv (state : GoalState) (env : Environment) : GoalState :=
  { state with savedState := { state.savedState with term := { state.savedState.term with
    meta := { state.savedState.term.meta with core := { state.savedState.term.meta.core with env } } } } }

private def withMCtx (state : GoalState) (mctx : MetavarContext) : GoalState :=
  { state with savedState := { state.savedState with term := { state.savedState.term with
    meta := { state.savedState.term.meta with meta := { state.metaState with mctx } } } } }

private def rejects (result : Except String CheckedTransition) : Bool := result.toOption.isNone

private def rejectsWith (fragment : String) (result : Except String CheckedTransition) : Bool :=
  match result with
  | .error message => (message.splitOn fragment).length > 1
  | .ok _ => false

/-- Add a declaration as the code generator does: without a kernel check. -/
private def addUnchecked (state : GoalState) (decl : Declaration) : Elab.TermElabM GoalState := do
  match state.env.addDeclWithoutChecking decl with
  | .ok env => return withEnv state env
  | .error _ => throwError "unchecked addition failed"

private def unsafeDefinition (name : Name) (type value : Expr) : Declaration :=
  .defnDecl { name, levelParams := [], type, value, hints := .opaque, safety := .unsafe, all := [name] }

private def safeDefinition (name : Name) (type value : Expr) : Declaration :=
  .defnDecl { name, levelParams := [], type, value, hints := .opaque, safety := .safe, all := [name] }

private def additions (state : GoalState) : List Name :=
  state.env.constants.foldStage2 (fun acc name _ => if state.trustedEnv.contains name then acc else name :: acc) []

private def tactic (state : GoalState) (text : String) (goal? : Option MVarId := none) :
    Elab.TermElabM (GoalState × Except String CheckedTransition) := do
  let some goal := goal?.orElse fun _ => state.goals.head? | throwError s!"{text}: no goal"
  -- The REPL runs each tactic in a fresh elaboration context over the saved state.
  let .success next ← (runTermElabM (state.tryTactic goal text) : CoreM _) | throwError s!"{text} failed"
  return (next, ← validateTransition state next goal)

private def splitter : Name := Name.mkNum `_private 0 ++ `Nat.pow.match_1.splitter

private def tests : Elab.TermElabM LSpec.TestSeq := do
  let mut tests := LSpec.TestSeq.done
  let .ok root ← goalStartExpr "∀ m n : Nat, Nat.pow m n = Nat.pow m n" #[] | throwError "start failed"
  let (intro, checked) ← tactic root "intro m n"
  let some intro := checked.toOption.map (·.state) | throwError "intro rejected"
  let (unfolded, checked) ← tactic intro "unfold Nat.pow"
  let compiled := (additions unfolded).filter fun name =>
    isCompilerRepresentation unfolded.env unfolded.trustedEnv name
  tests := tests ++ LSpec.test "the unfold leaves fresh compiler stage entries in the environment"
    (compiled.length == 3 && compiled.contains (splitter.str "_cstage2") && compiled.contains ((splitter.str "_rarg").str "_cstage2"))
  tests := tests ++ LSpec.test "a compiler-producing transition is accepted without hazards"
    (checked.toOption.any fun c => !c.hasSorry && !c.hasUnsafe && c.state.goals.length == 1)
  let some unfolded := checked.toOption.map (·.state) | throwError "unfold rejected"
  tests := tests ++ LSpec.test "the splitter itself is a kernel declaration"
    (classifyName unfolded.env unfolded.trustedEnv splitter == some .kernel)
  tests := tests ++ LSpec.test "inspection of the retained output validates"
    ((← validateSnapshot unfolded unfolded.goals).toOption.isSome)
  let (split, checked) ← tactic unfolded "split"
  tests := tests ++ LSpec.test "a later tactic continues the compiler-producing state"
    (checked.toOption.any (·.state.goals.length == 2))
  let some split := checked.toOption.map (·.state) | throwError "split rejected"
  let [_, sibling] := split.goals | throwError "split goals"
  let (_, checked) ← tactic split "rfl"
  let some first := checked.toOption.map (·.state) | throwError "first rfl rejected"
  -- The REPL resumes the dormant sibling; here it is selected explicitly.
  let (_, checked) ← tactic first "rfl" sibling
  let some done := checked.toOption.map (·.state) | throwError "second rfl rejected"
  let certificate ← certifyRoot done 200000
  let auxiliary := certificate.receipt?.map (·.auxiliary) |>.getD #[]
  tests := tests ++ LSpec.test "the original root certifies with kernel auxiliaries only"
    (certificate.status == "certified" && auxiliary.contains splitter.toString &&
      auxiliary.all fun name => (name.splitOn "_cstage").length == 1)

  -- A compiler entry is runtime data, never a proof dependency.
  let stage2 := splitter.str "_cstage2"
  let leaked := withMCtx done { done.mctx with eAssignment := done.mctx.eAssignment.insert done.root (mkConst stage2) }
  tests := tests ++ LSpec.test "the root proof cannot reference a compiler entry"
    (rejectsWith "Compiler-only declaration" (← validateSnapshot leaked))
  tests := tests ++ LSpec.test "certification rejects a compiler entry in the proof"
    ((← certifyRoot leaked 200000).status == "rejected")
  let user ← addUnchecked done (safeDefinition `Uses.compiler (mkConst ``Nat) (mkConst stage2))
  tests := tests ++ LSpec.test "a kernel declaration cannot reach compiler data after it was audited"
    (rejectsWith "Compiler-only declaration" (← validateSnapshot user))

  -- The exemption needs the compiler's registration, not the spelling.
  let named ← addUnchecked done (unsafeDefinition `Fake._cstage2 (mkConst `_obj) (mkConst `_neutral))
  tests := tests ++ LSpec.test "a stage-named entry without compiler IR keeps the kernel audit"
    (classifyName named.env named.trustedEnv `Fake._cstage2 == some .kernel &&
      rejectsWith "Missing proof dependency _obj" (← validateSnapshot named))
  let ordinary ← addUnchecked done (safeDefinition `Ordinary._cstage2 (mkConst ``Nat) (mkNatLit 0))
  tests := tests ++ LSpec.test "a well-formed kernel declaration named like a stage is checked, not exempted"
    (classifyName ordinary.env ordinary.trustedEnv `Ordinary._cstage2 == some .kernel &&
      (← validateSnapshot ordinary).toOption.isSome)
  let sentinel := withMCtx intro { intro.mctx with eAssignment := intro.mctx.eAssignment.insert intro.goals.head! (mkConst `_obj) }
  tests := tests ++ LSpec.test "a compiler sentinel in an ordinary kernel expression rejects"
    (rejectsWith "Missing proof dependency _obj" (← validateSnapshot sentinel))

  -- Registered compiler data still has to be well formed.
  let boxed := (splitter.str "_rarg").str "_boxed"
  let malformed ← addUnchecked done (unsafeDefinition (boxed.str "_cstage2") (mkConst `_obj) (mkConst `Missing.runtime))
  tests := tests ++ LSpec.test "registered compiler data with an unresolved reference is an integrity failure"
    (classifyName malformed.env malformed.trustedEnv (boxed.str "_cstage2") == some (.compiler 2 boxed) &&
      rejectsWith "unresolved compiler reference Missing.runtime" (← validateSnapshot malformed))
  let open_ ← addUnchecked done (unsafeDefinition (boxed.str "_cstage2") (mkConst `_obj) (.bvar 0))
  tests := tests ++ LSpec.test "registered compiler data must be closed"
    (rejectsWith "loose bound variable" (← validateSnapshot open_))
  tests := tests ++ LSpec.test "stage-1 representations cannot use stage-2 sentinels"
    (compilerEntryProblems done.env 1 (.defnInfo { name := `x, levelParams := [], type := mkConst `_obj, value := mkConst ``Nat, hints := .opaque, safety := .unsafe, all := [] }) != #[])

  -- Hazard accounting is unchanged for proof dependencies.
  let admission := mkApp2 (mkConst ``sorryAx [.zero]) done.rootType (mkConst ``Bool.false)
  let admitted := withMCtx done { done.mctx with eAssignment := done.mctx.eAssignment.insert done.root admission }
  tests := tests ++ LSpec.test "an admission in a compiler-producing proof is still reported"
    ((← validateSnapshot admitted).toOption.any (·.hasSorry) &&
      (← certifyRoot admitted 200000).status == "rejected")
  return tests

/-- The same transition on a session that has already run an unrelated tactic. -/
private def warmed : Elab.TermElabM LSpec.TestSeq := do
  let .ok warm ← goalStartExpr "True ∧ True" #[] | throwError "warm start failed"
  let .success _ ← warm.tryTactic warm.root "simp" | throwError "warm simp failed"
  let .ok root ← goalStartExpr "∀ m n : Nat, Nat.pow m (n+1) = Nat.pow m n * m" #[] | throwError "start failed"
  let (_, checked) ← tactic root "intro m n"
  let some intro := checked.toOption.map (·.state) | throwError "intro rejected"
  let (_, checked) ← tactic intro "rw [Nat.pow]"
  return LSpec.test "a rewrite with generated equations is accepted after earlier history"
    (checked.toOption.any fun c => !c.hasUnsafe && c.state.goals.length == 1)

def suite (env : Environment) : List (String × IO LSpec.TestSeq) := [
  ("Compiler-producing transitions", runTermElabMSeq env tests),
  ("Warmed session history", runTermElabMSeq env warmed)
]

end Pantograph.Test.CompilerValidation
