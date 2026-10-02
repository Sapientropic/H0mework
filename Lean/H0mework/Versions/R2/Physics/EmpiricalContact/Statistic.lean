import H0mework.Versions.R2.Physics.EmpiricalContact.Data

/-! A deterministic lower bound for the already frozen uniform component.
Only the small exponent 64 is numerically evaluated. No floating logarithm
or supplied verdict participates in this calculation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical

noncomputable section

/-- Exact binary-rational values read by Python from the frozen JSON table. -/
def frozenHigh : ℝ := 3844062731816691 / 9007199254740992
def frozenLow : ℝ := 659536895553805 / 9007199254740992

def uniformComponent (high low : ℝ) : ℝ :=
  ((1 / 4) / high) ^ highCount * ((1 / 4) / low) ^ lowCount

def uniformComponentAt (input : ReleasedContact) (high low : ℝ) : ℝ :=
  ((1 / 4) / high) ^ highCountAt input.table *
    ((1 / 4) / low) ^ lowCountAt input.table

def contactResidual (input : ReleasedContact) : ℝ :=
  uniformComponentAt input frozenHigh frozenLow / 7 - 40

def uniformMixtureResidual (high low : ℝ) : ℝ := uniformComponent high low / 7 - 40

theorem frozen_bounds :
    0 < frozenHigh ∧ frozenHigh ≤ 1 / 2 ∧
    0 < frozenLow ∧ frozenLow ≤ 1 / 12 := by
  norm_num [frozenHigh, frozenLow]

theorem uniformComponent_gt_threshold (high low : ℝ)
    (high_positive : 0 < high) (high_upper : high ≤ 1 / 2)
    (low_positive : 0 < low) (low_upper : low ≤ 1 / 12) :
    280 < uniformComponent high low := by
  have high_ratio : (1 / 2 : ℝ) ≤ (1 / 4) / high := by
    apply (le_div_iff₀ high_positive).2
    linarith
  have low_ratio : (3 : ℝ) ≤ (1 / 4) / low := by
    apply (le_div_iff₀ low_positive).2
    linarith
  have high_exponent : (1 / 2 : ℝ) ^ (3 * 24577) ≤ (1 / 2 : ℝ) ^ 50846 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by decide)
  have grouped : (9 / 8 : ℝ) ^ 24577 =
      (1 / 2 : ℝ) ^ (3 * 24577) * (3 : ℝ) ^ (2 * 24577) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    congr 1
    norm_num
  have large : (9 / 8 : ℝ) ^ 64 ≤ (9 / 8 : ℝ) ^ 24577 :=
    pow_le_pow_right₀ (by norm_num) (by decide)
  have small : (280 : ℝ) < (9 / 8 : ℝ) ^ 64 := by norm_num
  apply lt_of_lt_of_le (lt_of_lt_of_le small large)
  rw [grouped, uniformComponent, highCount_value, lowCount_value]
  apply mul_le_mul
  · exact high_exponent.trans (pow_le_pow_left₀ (by norm_num) high_ratio _)
  · exact pow_le_pow_left₀ (by norm_num) low_ratio _
  · positivity
  · positivity

theorem frozen_uniform_residual_positive : 0 < uniformMixtureResidual frozenHigh frozenLow := by
  obtain ⟨hp, hu, lp, lu⟩ := frozen_bounds
  have crossing := uniformComponent_gt_threshold frozenHigh frozenLow hp hu lp lu
  unfold uniformMixtureResidual
  linarith

theorem released_contact_residual_positive : 0 < contactResidual releasedContact :=
  frozen_uniform_residual_positive

/-- The remaining six components need only their intrinsic nonnegativity.
This is the original fixed 1/7 mixture, not a newly selected test. -/
theorem frozen_mixture_rejected (otherComponents : Fin 6 → ℝ)
    (nonnegative : ∀ i, 0 ≤ otherComponents i) :
    40 < (uniformComponent frozenHigh frozenLow + ∑ i, otherComponents i) / 7 := by
  have sum_nonnegative : 0 ≤ ∑ i, otherComponents i := Finset.sum_nonneg fun i _ => nonnegative i
  have residual := frozen_uniform_residual_positive
  unfold uniformMixtureResidual at residual
  linarith

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical
