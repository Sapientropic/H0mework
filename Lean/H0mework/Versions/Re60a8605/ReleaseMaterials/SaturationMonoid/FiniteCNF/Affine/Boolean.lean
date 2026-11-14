import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Acceptance
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Cone

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Boolean

open InterferenceProgram

def anyOver : List Nat → ((Nat → Bool) → Bool) → (Nat → Bool) → Bool
  | [], value, environment => value environment
  | i :: rest, value, environment =>
      anyOver rest value (Function.update environment i false) ||
        anyOver rest value (Function.update environment i true)

theorem anyOver_congr (indices : List Nat) (left right : (Nat → Bool) → Bool)
    (same : ∀ environment, left environment = right environment) (environment : Nat → Bool) :
    anyOver indices left environment = anyOver indices right environment := by
  induction indices generalizing environment with
  | nil => exact same environment
  | cons i rest ih => simp only [anyOver, ih]

theorem anyOver_constant (indices : List Nat) (b : Bool) (environment : Nat → Bool) :
    anyOver indices (fun _ => b) environment = b := by
  induction indices generalizing environment with
  | nil => rfl
  | cons i rest ih => simp only [anyOver, ih, Bool.or_self]

def constant (b : Bool) : Program := InterferenceDecision.fromAmplitude (Fragment.constant (bit b))

theorem eval_constant (b : Bool) (environment : Nat → Bool) :
    (constant b).eval environment = bit b := by
  rw [constant, InterferenceDecision.eval_fromAmplitude, Fragment.eval_constant]

def existential (program : Program) (i : Nat) : Program :=
  let left := InterferenceDecision.amplitude (program.cofactor i false)
  let right := InterferenceDecision.amplitude (program.cofactor i true)
  InterferenceDecision.fromAmplitude (left.not.and right.not).not

theorem eval_existential (program : Program) (i : Nat) (environment : Nat → Bool) :
    (existential program i).eval environment = bit
      (truth (program.eval (Function.update environment i false)) ||
        truth (program.eval (Function.update environment i true))) := by
  simp only [existential, InterferenceDecision.eval_fromAmplitude, Fragment.eval_not,
    Fragment.eval_and, truth_bit, InterferenceDecision.eval_amplitude, Program.eval_cofactor,
    Bool.not_and, Bool.not_not]

structure Prepared where
  program : Program
  terminal : Option Bool

/-- Both roots are read from the same actual intern table used to generate the shared program. -/
def prepare (program : Program) : Prepared :=
  let generated := Reduce.smartCompact program.code
  let bound := (Reduce.smartCompact_represents program.code (fun _ => false)).2.2.2.1
  let weight := generated.mapping.getD program.weight.val 0
  let phase := generated.mapping.getD program.phase.val 0
  let code : Program := ⟨generated.state.code, ⟨weight, bound program.weight.val⟩,
    ⟨phase, bound program.phase.val⟩⟩
  let terminal := do
    let w ← Reduce.known weight generated.state.table
    let p ← Reduce.known phase generated.state.table
    pure (truth (w * sign p))
  ⟨code, terminal⟩

theorem prepare_program (program : Program) : (prepare program).program = program.share := rfl

theorem prepare_eval (program : Program) (environment : Nat → Bool) :
    (prepare program).program.eval environment = program.eval environment := Program.eval_share _ _

theorem prepare_terminal (program : Program) (b : Bool) (found : (prepare program).terminal = some b)
    (environment : Nat → Bool) : truth (program.eval environment) = b := by
  let generated := Reduce.smartCompact program.code
  have valid := (Reduce.smartCompact_represents program.code environment).1
  change Option.bind (Reduce.known (generated.mapping.getD program.weight.val 0) generated.state.table)
    (fun w => Option.bind (Reduce.known (generated.mapping.getD program.phase.val 0) generated.state.table)
      (fun p => some (truth (w * sign p)))) = some b at found
  cases weight : Reduce.known (generated.mapping.getD program.weight.val 0) generated.state.table with
  | none => simp only [weight, Option.bind_none, reduceCtorEq] at found
  | some w =>
      cases phase : Reduce.known (generated.mapping.getD program.phase.val 0) generated.state.table with
      | none => simp only [weight, phase, Option.bind_some, Option.bind_none, reduceCtorEq] at found
      | some p =>
          have result : truth (w * sign p) = b := by
            simpa only [weight, phase, Option.bind_some, Option.some.injEq] using found
          have wValue := Reduce.known_sound generated.state valid environment _ w weight
          have pValue := Reduce.known_sound generated.state valid environment _ p phase
          change truth ((run environment program.code).getD program.weight.val 0 *
            sign ((run environment program.code).getD program.phase.val 0)) = b
          rw [← Reduce.smartCompact_reads program.code environment program.weight.val,
            ← Reduce.smartCompact_reads program.code environment program.phase.val]
          change truth ((run environment generated.state.code).getD (generated.mapping.getD program.weight.val 0) 0 *
            sign ((run environment generated.state.code).getD (generated.mapping.getD program.phase.val 0) 0)) = b
          rw [wValue, pValue]
          exact result

def fold : List Nat → Program → Program
  | [], program => program
  | i :: rest, program =>
      let previous := prepare (fold rest program)
      match previous.terminal with
      | some b => constant b
      | none => Cone.pruneCone (existential previous.program i)

theorem eval_fold (indices : List Nat) (program : Program) (environment : Nat → Bool) :
    truth ((fold indices program).eval environment) =
      anyOver indices (fun env => truth (program.eval env)) environment := by
  induction indices generalizing environment with
  | nil => rfl
  | cons i rest ih =>
      cases known : (prepare (fold rest program)).terminal with
      | none =>
          simp only [fold, known, Cone.eval_pruneCone, eval_existential, truth_bit, prepare_eval, anyOver, ih]
      | some b =>
          have all := prepare_terminal (fold rest program) b known
          simp only [fold, known, eval_constant, truth_bit, anyOver]
          rw [← ih, ← ih, all, all, Bool.or_self]

theorem anyOver_rangeFrom (width offset : Nat) (value : (Nat → Bool) → Bool)
    (environment : Nat → Bool) :
    anyOver (List.range' offset width) value environment = true ↔
      ∃ parameters : Assignment width,
        value (InterferenceDecision.fill environment offset parameters) = true := by
  induction width generalizing offset environment with
  | zero => simp [anyOver]
  | succ width ih =>
      rw [List.range'_succ, anyOver, Bool.or_eq_true, ih, ih, Fin.exists_fin_succ_pi]
      simp only [Bool.exists_bool, InterferenceDecision.fill_succ]

theorem anyOver_range (width : Nat) (value : (Nat → Bool) → Bool) :
    anyOver (List.range width) value InterferenceDecision.zeroEnvironment = true ↔
      ∃ parameters : Assignment width, value (extendAssignment parameters) = true := by
  simpa only [List.range_eq_range', Acceptance.fill_zero_eq_extend] using
    anyOver_rangeFrom width 0 value InterferenceDecision.zeroEnvironment

def close {n : Nat} (freeWidth : Nat) (coordinates : Array Row) (formula : CNFFormula n) : Program :=
  fold (List.range freeWidth) (Cone.pruneCone (Acceptance.compile coordinates formula))

def decideWith {n : Nat} (freeWidth : Nat) (coordinates : Array Row) (formula : CNFFormula n) : Bool :=
  truth (InterferenceDecision.readProgram (close freeWidth coordinates formula)).value

theorem decideWith_correct {n freeWidth : Nat} (coordinates : Array Row) (formula : CNFFormula n) :
    decideWith freeWidth coordinates formula = true ↔ ∃ parameters : Assignment freeWidth,
      CNFFormula.eval formula (extendAssignment (Gates.lift n coordinates parameters)) = true := by
  simp only [decideWith, InterferenceDecision.readProgram_value, close, eval_fold, anyOver_range]
  simp only [Cone.eval_pruneCone, Acceptance.eval_compile, truth_bit]
  apply exists_congr
  intro parameters
  have equation := formula_eval_restrict formula (Gates.coordinate coordinates (extendAssignment parameters))
  exact Eq.to_iff (congrArg (· = true) equation.symm)

theorem existential_size (program : Program) (i : Nat) :
    (existential program i).code.size = 2 * program.code.size + 9 := by
  simp [existential, InterferenceDecision.fromAmplitude, Fragment.not, Fragment.unary,
    Fragment.and, Fragment.binary, InterferenceDecision.amplitude_size]
  omega

theorem constant_size (b : Bool) : (constant b).code.size = 2 := by
  simp [constant, InterferenceDecision.fromAmplitude, Fragment.constant]

def nodeBudget : Nat → Nat → Nat
  | 0, nodes => nodes
  | steps+1, nodes => 2 * nodeBudget steps nodes + 12

theorem fold_size (indices : List Nat) (program : Program) :
    (fold indices program).code.size ≤ nodeBudget indices.length program.code.size := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      cases known : (prepare (fold rest program)).terminal with
      | none =>
          have trimmed := Cone.pruneCone_size (existential (prepare (fold rest program)).program i)
          have shared := Program.share_size (fold rest program)
          simp only [existential_size, prepare_program] at trimmed
          simp only [fold, known, List.length_cons, nodeBudget, prepare_program]
          omega
      | some b =>
          simp only [fold, known, constant_size, List.length_cons, nodeBudget]
          omega

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Boolean
