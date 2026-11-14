import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.Proposition828
import H0mework.Foundation.Finite.EffectiveCoefficient
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Original CNF source and its finite zero-spectrum program

This subordinate mathematical producer uses the original P687 CNF evaluator and
P828 indexed residual. Its rational polynomial acts on the actual finite
assignment source; the zero coefficient is consumed by the existing finite
effective-coefficient kernel. Evaluation over all assignments is an exact
semantic readout, with no machine-time assertion.
-/

namespace SaturationMonoid.ComplexityProjection.SATSource

open Polynomial
open scoped BigOperators

abbrev Assignment (n : Nat) := Fin n → Bool

/-- Extend the actual finite assignment by false outside the formula's variables. -/
def extendAssignment {n : Nat} (assignment : Assignment n) : Nat → Bool :=
  fun i => if hi : i < n then assignment ⟨i, hi⟩ else false

@[simp] theorem extendAssignment_apply {n : Nat} (assignment : Assignment n) (i : Fin n) :
    extendAssignment assignment i.val = assignment i := by
  simp [extendAssignment]

theorem clause_eval_restrict {n : Nat} (clause : CNFClause n)
    (assignment : Nat → Bool) :
    CNFClause.eval clause (extendAssignment fun i : Fin n => assignment i.val) =
      CNFClause.eval clause assignment := by
  simp only [CNFClause.eval]
  congr 1
  funext lit
  simp [CNFLiteral.eval]

theorem formula_eval_restrict {n : Nat} (formula : CNFFormula n)
    (assignment : Nat → Bool) :
    CNFFormula.eval formula (extendAssignment fun i : Fin n => assignment i.val) =
      CNFFormula.eval formula assignment := by
  simp only [CNFFormula.eval]
  congr 1
  funext clause
  exact clause_eval_restrict clause assignment

/-- Finite assignment transport preserves the original satisfiability predicate. -/
theorem satisfiable_iff_finite_assignment {n : Nat} (formula : CNFFormula n) :
    CNFSatisfiable formula ↔
      ∃ assignment : Assignment n,
        CNFFormula.eval formula (extendAssignment assignment) = true := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨fun i => assignment i.val, (formula_eval_restrict formula assignment).trans satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨extendAssignment assignment, satisfies⟩

/-- The count retains the original clause indices, including repeated clauses. -/
def violationCount {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) : Nat :=
  ∑ i : Fin formula.length,
    if CNFClause.eval (formula.get i) (extendAssignment assignment) = true then 0 else 1

theorem violationCount_le_length {n : Nat} (formula : CNFFormula n)
    (assignment : Assignment n) : violationCount formula assignment ≤ formula.length := by
  calc
    violationCount formula assignment ≤ ∑ _i : Fin formula.length, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> omega
    _ = formula.length := by simp

/-- The integer count is the original real indexed residual energy. -/
theorem violationCount_cast_eq_energy {n : Nat} (formula : CNFFormula n)
    (assignment : Assignment n) :
    (violationCount formula assignment : ℝ) =
      phaseResidualEnergy (CNFIndexedClauseResidual formula (extendAssignment assignment)) := by
  simp only [violationCount, Nat.cast_sum, phaseResidualEnergy]
  apply Finset.sum_congr rfl
  intro i _
  by_cases satisfies : CNFClause.eval (formula.get i) (extendAssignment assignment) = true
  · simp [CNFIndexedClauseResidual]
  · simp [CNFIndexedClauseResidual]

theorem violationCount_eq_zero_iff_eval {n : Nat} (formula : CNFFormula n)
    (assignment : Assignment n) :
    violationCount formula assignment = 0 ↔
      CNFFormula.eval formula (extendAssignment assignment) = true := by
  constructor
  · intro countZero
    apply (cnfIndexedResidualEnergy_zero_iff_formula_eval
      formula (extendAssignment assignment)).mp
    rw [← violationCount_cast_eq_energy, countZero]
    norm_num
  · intro satisfies
    have energyZero := (cnfIndexedResidualEnergy_zero_iff_formula_eval
      formula (extendAssignment assignment)).mpr satisfies
    rw [← violationCount_cast_eq_energy] at energyZero
    exact_mod_cast energyZero

/-- The product over the known integer energy window, without computing a spectrum. -/
noncomputable def annihilator (m : Nat) : Polynomial ℚ :=
  ∏ r ∈ Finset.range (m + 1), (X - C (r : ℚ))

/-- The exact rational zero-spectrum filter, generated from the number of clauses. -/
noncomputable def zeroFilter (m : Nat) : Polynomial ℚ :=
  ∏ r ∈ Finset.range m, (1 - C ((r + 1 : ℚ)⁻¹) * X)

@[simp] theorem zeroFilter_eval_zero (m : Nat) : (zeroFilter m).eval 0 = 1 := by
  simp [zeroFilter, Polynomial.eval_prod]

theorem annihilator_eval_nat (m k : Nat) (hk : k ≤ m) :
    (annihilator m).eval (k : ℚ) = 0 := by
  rw [annihilator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (m + 1))
  simp

theorem zeroFilter_eval_nat_of_pos (m k : Nat) (hk : 0 < k) (hkm : k ≤ m) :
    (zeroFilter m).eval (k : ℚ) = 0 := by
  rw [zeroFilter, Polynomial.eval_prod]
  apply Finset.prod_eq_zero
    (Finset.mem_range.mpr (by omega) : k - 1 ∈ Finset.range m)
  have hsub : k - 1 + 1 = k := by omega
  have hcast : ((k - 1 : Nat) : ℚ) + 1 = k := by exact_mod_cast hsub
  have hnonzero : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [hcast, hnonzero]

theorem zeroFilter_eval_nat (m k : Nat) (hk : k ≤ m) :
    (zeroFilter m).eval (k : ℚ) = if k = 0 then 1 else 0 := by
  by_cases hzero : k = 0
  · simp [hzero]
  · rw [if_neg hzero]
    exact zeroFilter_eval_nat_of_pos m k (Nat.pos_of_ne_zero hzero) hk

/-- The actual source action satisfies the explicit degree `m + 1` relation. -/
theorem annihilator_eval_violationCount {n : Nat} (formula : CNFFormula n)
    (assignment : Assignment n) :
    (annihilator formula.length).eval (violationCount formula assignment : ℚ) = 0 :=
  annihilator_eval_nat _ _ (violationCount_le_length formula assignment)

/-- The filter reads exactly the original formula truth on every original assignment. -/
theorem zeroFilter_eval_violationCount {n : Nat} (formula : CNFFormula n)
    (assignment : Assignment n) :
    (zeroFilter formula.length).eval (violationCount formula assignment : ℚ) =
      if CNFFormula.eval formula (extendAssignment assignment) = true then 1 else 0 := by
  rw [zeroFilter_eval_nat _ _ (violationCount_le_length formula assignment)]
  simp only [violationCount_eq_zero_iff_eval]

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedFiniteEffectiveCoefficient SourceGeneratedEffectiveFibreDisposition

/-- The original coefficient kernel counts actual satisfying assignments. -/
theorem effectiveCoefficient_pos_iff_satisfiable {n : Nat} (formula : CNFFormula n) :
    0 < effectiveCoefficient (violationCount formula) 0 ↔ CNFSatisfiable formula := by
  rw [effectiveCoefficient_pos_iff_fibre, satisfiable_iff_finite_assignment]
  constructor
  · rintro ⟨⟨assignment, hzero⟩⟩
    exact ⟨assignment, (violationCount_eq_zero_iff_eval formula assignment).mp hzero⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨⟨assignment, (violationCount_eq_zero_iff_eval formula assignment).mpr satisfies⟩⟩

theorem effectiveCoefficient_eq_zero_iff_unsatisfiable {n : Nat}
    (formula : CNFFormula n) :
    effectiveCoefficient (violationCount formula) 0 = 0 ↔ ¬ CNFSatisfiable formula := by
  rw [← effectiveCoefficient_pos_iff_satisfiable]
  omega

end SaturationMonoid.ComplexityProjection.SATSource
