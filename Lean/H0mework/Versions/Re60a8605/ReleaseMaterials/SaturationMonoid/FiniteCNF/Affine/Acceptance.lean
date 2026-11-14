import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Gates

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Acceptance

open InterferenceProgram
open scoped BigOperators

def original {n : Nat} : CNFFormula n → Fragment
  | [] => Fragment.constant 1
  | clause :: rest => (compileClause clause).not.and (original rest)

theorem eval_original {n : Nat} (formula : CNFFormula n) (environment : Nat → Bool) :
    (original formula).eval environment = bit (CNFFormula.eval formula environment) := by
  induction formula with
  | nil => simp [original, Fragment.eval_constant, CNFFormula.eval, bit]
  | cons clause rest ih =>
      simp only [original, Fragment.eval_and, Fragment.eval_not, eval_compileClause, ih,
        truth_bit, Bool.not_not, CNFFormula.eval, List.all_cons]

def compile {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) : Program :=
  let source := Gates.compileRows coordinates.toList
  let accepted := InterferenceDecision.fromAmplitude (original formula)
  let code := source.code ++ accepted.code.map (Gates.rewriteNode n 0 source.code.size source.outputs)
  ⟨code,
    ⟨source.code.size + accepted.weight.val, by
      simpa only [code, Array.size_append, Array.size_map] using
        Nat.add_lt_add_left accepted.weight.isLt source.code.size⟩,
    ⟨source.code.size + accepted.phase.val, by
      simpa only [code, Array.size_append, Array.size_map] using
        Nat.add_lt_add_left accepted.phase.isLt source.code.size⟩⟩

theorem run_compile {n : Nat} (coordinates : Array Row) (formula : CNFFormula n)
    (environment : Nat → Bool) :
    run environment (compile coordinates formula).code =
      run environment (Gates.compileRows coordinates.toList).code ++
        run (Gates.originalEnvironment n 0 coordinates environment)
          (InterferenceDecision.fromAmplitude (original formula)).code := by
  simp only [compile, run, Array.toList_append, Array.toList_map, runCode_append]
  have equation := Gates.runCode_rewrite n 0 coordinates environment #[]
    (InterferenceDecision.fromAmplitude (original formula)).code.toList
  simp only [Array.append_empty] at equation
  exact equation

theorem eval_compile {n : Nat} (coordinates : Array Row) (formula : CNFFormula n)
    (environment : Nat → Bool) :
    (compile coordinates formula).eval environment =
      bit (CNFFormula.eval formula (Gates.coordinate coordinates environment)) := by
  have value : (compile coordinates formula).eval environment =
      (InterferenceDecision.fromAmplitude (original formula)).eval
        (Gates.originalEnvironment n 0 coordinates environment) := by
    simp only [Program.eval]
    rw [run_compile]
    simp only [compile]
    rw [← run_size environment (Gates.compileRows coordinates.toList).code,
      getD_append_right, getD_append_right]
  rw [value, InterferenceDecision.eval_fromAmplitude, eval_original]
  rw [← formula_eval_restrict formula (Gates.originalEnvironment n 0 coordinates environment),
    ← formula_eval_restrict formula (Gates.coordinate coordinates environment)]
  congr 3
  funext i
  simp [Gates.originalEnvironment, i.isLt]

def close {n : Nat} (freeWidth : Nat) (coordinates : Array Row) (formula : CNFFormula n) : Program :=
  InterferenceDecision.eliminateAll (List.range freeWidth) (compile coordinates formula).share

theorem fill_zero_eq_extend {width : Nat} (parameters : Assignment width) :
    InterferenceDecision.fill InterferenceDecision.zeroEnvironment 0 parameters =
      extendAssignment parameters := by
  funext i
  simp only [InterferenceDecision.fill, Nat.zero_le, Nat.zero_add, true_and, Nat.sub_zero,
    extendAssignment]
  split <;> rfl

theorem eval_close {n freeWidth : Nat} (coordinates : Array Row) (formula : CNFFormula n) :
    (close freeWidth coordinates formula).eval InterferenceDecision.zeroEnvironment =
      ∑ parameters : Assignment freeWidth,
        bit (CNFFormula.eval formula (extendAssignment (Gates.lift n coordinates parameters))) := by
  rw [close, InterferenceDecision.eval_eliminateAll, InterferenceDecision.sumOver_range]
  apply Finset.sum_congr rfl
  intro parameters _
  rw [Program.eval_share, eval_compile, fill_zero_eq_extend]
  exact congrArg bit (formula_eval_restrict formula (Gates.coordinate coordinates (extendAssignment parameters))).symm

theorem bit_nonnegative (value : Bool) : (0 : ℤ) ≤ bit value := by cases value <;> decide

theorem bit_positive (value : Bool) : (0 : ℤ) < bit value ↔ value = true := by cases value <;> decide

def decideWith {n : Nat} (freeWidth : Nat) (coordinates : Array Row) (formula : CNFFormula n) : Bool :=
  decide (0 < (InterferenceDecision.readProgram (close freeWidth coordinates formula)).value)

theorem decideWith_correct {n freeWidth : Nat} (coordinates : Array Row) (formula : CNFFormula n) :
    decideWith freeWidth coordinates formula = true ↔ ∃ parameters : Assignment freeWidth,
      CNFFormula.eval formula (extendAssignment (Gates.lift n coordinates parameters)) = true := by
  simp only [decideWith, decide_eq_true_eq, InterferenceDecision.readProgram_value, eval_close]
  rw [Finset.sum_pos_iff_of_nonneg (fun parameters _ => bit_nonnegative _)]
  simp only [Finset.mem_univ, true_and, bit_positive]

theorem original_size {n : Nat} (formula : CNFFormula n) :
    (original formula).code.size ≤ 1 + 3 * formula.length + 3 * SATJoint.literalCount formula := by
  induction formula with
  | nil => simp [original, Fragment.constant, SATJoint.literalCount]
  | cons clause rest ih =>
      have first := InterferenceDecision.compileClause_size clause
      simp only [original, Fragment.and, Fragment.binary, Fragment.not, Fragment.unary,
        Array.size_push, Array.size_append, Array.size_map, List.length_cons]
      simp only [SATJoint.literalCount, List.map_cons, List.sum_cons] at *
      omega

def initialNodes {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) : Nat :=
  3 + coordinates.size + 2 * Gates.rowTerms coordinates.toList +
    3 * formula.length + 3 * SATJoint.literalCount formula

theorem compile_size {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) :
    (compile coordinates formula).code.size ≤ initialNodes coordinates formula := by
  have bound := original_size formula
  simp only [compile, Array.size_append, Array.size_map, Gates.compileRows_size,
    InterferenceDecision.fromAmplitude, Array.size_push, Array.length_toList, initialNodes]
  omega

theorem close_size {n : Nat} (freeWidth : Nat) (coordinates : Array Row) (formula : CNFFormula n) :
    (close freeWidth coordinates formula).code.size ≤
      InterferenceDecision.nodeBudget freeWidth (compile coordinates formula).share.code.size := by
  exact (InterferenceDecision.eliminateAll_size (List.range freeWidth) _).trans_eq
    (by rw [List.length_range])

theorem close_reading {n : Nat} (freeWidth : Nat) (coordinates : Array Row) (formula : CNFFormula n) :
    (InterferenceDecision.readProgram (close freeWidth coordinates formula)).nodeVisits ≤
      InterferenceDecision.nodeBudget freeWidth (compile coordinates formula).share.code.size ∧
    (InterferenceDecision.readProgram (close freeWidth coordinates formula)).rootReads = 2 := by
  have reading := InterferenceDecision.readProgram_visits (close freeWidth coordinates formula)
  exact ⟨reading.1.le.trans (close_size freeWidth coordinates formula), reading.2⟩

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Acceptance
