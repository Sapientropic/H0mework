import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.Operator

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse

abbrev JordanMatrix := Matrix (Fin 2) (Fin 2) ℂ

private def block (a b : ℂ) : JordanMatrix :=
  !![a, b; 0, a]

private theorem block_mul (a b c e : ℂ) :
    block a b * block c e = block (a * c) (a * e + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block, Matrix.mul_apply, Fin.sum_univ_two]

private theorem block_one : block 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block]

private theorem one_add_block (z : ℂ) :
    (1 : JordanMatrix) + block 0 z = block 1 z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block]

private theorem block_sub_one (z : ℂ) :
    block 0 z - (1 : JordanMatrix) = block (-1) z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block]

private theorem block_norm (a b : ℂ) : ‖block a b‖ = ‖a‖ + ‖b‖ := by
  rw [Matrix.linfty_opNorm_def]
  have all : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [all, Finset.sup_insert, Finset.sup_singleton]
  simp [block]

/-- The scaled Jordan block attains the Cayley inverse bound for every positive step. -/
def jordan (d : ℝ) : JordanMatrix := block 0 (d : ℂ)⁻¹

theorem jordan_cayley_power_norm {d : ℝ} (positive : 0 < d) (n : ℕ) :
    ‖(cayley (jordan d) d)^n‖ = (n : ℝ) + 1 := by
  have nonzero : (d : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  have action : (d : ℂ) • jordan d = block 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordan, block, Matrix.smul_apply, smul_eq_mul, nonzero]
  have powers (m : ℕ) : (block 1 1)^m = block 1 (m : ℂ) := by
    induction m with
    | zero => simpa using block_one.symm
    | succ m inductionHypothesis =>
      rw [pow_succ, inductionHypothesis, block_mul]
      simp [Nat.cast_succ, add_comm]
  rw [cayley, action, one_add_block, powers, block_norm]
  simp [add_comm]

theorem jordan_inverse_attains {d : ℝ} (positive : 0 < d) :
    ‖inverse (jordan d) d‖ = inverseBudget d 1 ∧
      ‖inverse (jordan d) d‖ = (1 + d) / d := by
  have growth (n : ℕ) : ‖(cayley (jordan d) d)^n‖ ≤ ((n : ℝ) + 1) * 1 := by
    rw [jordan_cayley_power_norm positive, mul_one]
  have right :
      (jordan d - 1) * block (-1) (-(d : ℂ)⁻¹) = 1 := by
    rw [jordan, block_sub_one, block_mul]
    simp [block_one]
  have explicit : inverse (jordan d) d = block (-1) (-(d : ℂ)⁻¹) := by
    calc
      _ = inverse (jordan d) d * ((jordan d - 1) * block (-1) (-(d : ℂ)⁻¹)) := by
        rw [right, mul_one]
      _ = _ := by rw [← mul_assoc, (inverse_effect (jordan d) positive growth).1, one_mul]
  have formula : ‖inverse (jordan d) d‖ = (1 + d) / d := by
    rw [explicit, block_norm, norm_neg, norm_neg, norm_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos positive]
    field_simp [positive.ne']; ring
  refine ⟨formula.trans ?_, formula⟩
  unfold inverseBudget
  change (1 + d) / d = d * (1 + d)⁻¹ * (1 / (1 - (1 + d)⁻¹)^2)
  have denominator : (1 + d) ≠ 0 := (by positivity : 0 < 1 + d).ne'
  field_simp [positive.ne', denominator]; ring

end SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
