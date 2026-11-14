import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedFiniteInverseWord

open scoped BigOperators

section Algebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

def relative (damping : ℂ) (compensation : A) : A :=
  damping⁻¹ • compensation

/-- The actual finite action word for a scalar-shifted compensation. -/
def word (damping : ℂ) (compensation : A) (length : Nat) : A :=
  damping⁻¹ • ∑ i ∈ Finset.range length, relative damping compensation ^ i

private theorem clock_factor (damping : ℂ) (nonzero : damping ≠ 0) (compensation : A) :
    damping • (1 - relative damping compensation) = damping • (1 : A) - compensation := by
  rw [relative, smul_sub, smul_smul, mul_inv_cancel₀ nonzero, one_smul]

theorem clock_word (damping : ℂ) (nonzero : damping ≠ 0) (compensation : A) (length : Nat) :
    (damping • (1 : A) - compensation) * word damping compensation length =
      1 - relative damping compensation ^ length := by
  rw [← clock_factor damping nonzero compensation, word, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ nonzero, one_smul, mul_neg_geom_sum]

theorem word_clock (damping : ℂ) (nonzero : damping ≠ 0) (compensation : A) (length : Nat) :
    word damping compensation length * (damping • (1 : A) - compensation) =
      1 - relative damping compensation ^ length := by
  rw [← clock_factor damping nonzero compensation, word, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ nonzero, one_smul, geom_sum_mul_neg]

end Algebra

/-- A strict tail cutoff paid by the relative loss and input budget. -/
def cutoff (loss budget tolerance : ℝ) : Nat :=
  ⌈Real.log (1+budget/tolerance) / loss⌉₊ + 1

theorem cutoff_pays (loss budget tolerance : ℝ) (lossPos : 0 < loss) (lossLe : loss ≤ 1)
    (budgetNonneg : 0 ≤ budget) (tolerancePos : 0 < tolerance) :
    (1-loss)^cutoff loss budget tolerance * budget < tolerance := by
  let level := 1+budget/tolerance
  let count := cutoff loss budget tolerance
  have levelPos : 0 < level := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg budgetNonneg tolerancePos.le)
  have after : Real.log level / loss < (count : ℝ) :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_succ_self ⌈Real.log level / loss⌉₊)
  have exponential : (1-loss)^count ≤ Real.exp (-(count : ℝ)*loss) := by
    rw [show -(count : ℝ)*loss = (count : ℝ)*(-loss) by ring, Real.exp_nat_mul]
    have base : 1-loss ≤ Real.exp (-loss) := by
      simpa only [neg_add_eq_sub] using Real.add_one_le_exp (-loss)
    exact pow_le_pow_left₀ (sub_nonneg.mpr lossLe) base count
  have decayed : Real.exp (-(count : ℝ)*loss) < level⁻¹ := by
    rw [← Real.exp_log levelPos, ← Real.exp_neg]
    exact Real.exp_lt_exp.mpr (by linarith only [(div_lt_iff₀ lossPos).mp after])
  have levelPrice : tolerance * level = tolerance + budget := by
    dsimp only [level]
    rw [mul_add, mul_one, mul_comm tolerance, div_mul_cancel₀ _ tolerancePos.ne']
  calc
    _ ≤ Real.exp (-(count : ℝ)*loss) * budget := mul_le_mul_of_nonneg_right exponential budgetNonneg
    _ ≤ level⁻¹ * budget := mul_le_mul_of_nonneg_right decayed.le budgetNonneg
    _ < tolerance := by
      rw [mul_comm, ← div_eq_mul_inv, div_lt_iff₀ levelPos, levelPrice]
      exact lt_add_of_pos_left _ tolerancePos

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedFiniteInverseWord
