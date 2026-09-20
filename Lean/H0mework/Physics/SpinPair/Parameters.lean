import H0mework.Physics.Source.EnrichedProofFreeSource
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Positive parameters of the same-source homogeneous spin/gauge balance.
The lapse is generated with the amplitudes; it is not fixed before varying
the native coframe-dependent constitutive action. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource

noncomputable section

def sourceCoupling : ℝ := positiveSmoothUnifiedSource.legacy.sigma
def spinScale : ℝ := Real.sqrt 2
def gaugeScale : ℝ := 3 * spinScale / 5
def lapse : ℝ := Real.sqrt (54 / 125)
def frequency : ℝ := 3 * lapse / 2 * (spinScale - gaugeScale)

theorem sourceCoupling_eq : sourceCoupling = 1 / 2 := positiveSource_sigma

theorem spinScale_pos : 0 < spinScale := Real.sqrt_pos.2 (by norm_num)
theorem spinScale_sq : spinScale ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem gaugeScale_pos : 0 < gaugeScale :=
  div_pos (mul_pos (by norm_num) spinScale_pos) (by norm_num)
theorem lapse_pos : 0 < lapse := Real.sqrt_pos.2 (by norm_num)
theorem lapse_sq : lapse ^ 2 = 54 / 125 := Real.sq_sqrt (by norm_num)

private theorem spinScale_cube : spinScale ^ 3 = 2 * spinScale := by
  calc
    spinScale ^ 3 = spinScale ^ 2 * spinScale := by ring
    _ = 2 * spinScale := by rw [spinScale_sq]

private theorem spinScale_fourth : spinScale ^ 4 = 4 := by
  calc
    spinScale ^ 4 = (spinScale ^ 2) ^ 2 := by ring
    _ = 4 := by rw [spinScale_sq]; norm_num

theorem spin_gauge_product : spinScale * gaugeScale = 6 / 5 := by
  unfold gaugeScale
  nlinarith [spinScale_sq]

theorem gauge_cubic_balance :
    gaugeScale ^ 3 = 2 * sourceCoupling * lapse ^ 2 * spinScale := by
  rw [sourceCoupling_eq, lapse_sq]
  simp only [gaugeScale, div_pow, mul_pow, spinScale_cube]
  ring

theorem coframe_time_balance :
    3 * gaugeScale ^ 4 / (4 * sourceCoupling * lapse ^ 2) -
      6 * (spinScale - gaugeScale) * spinScale = 3 - 3 * spinScale ^ 2 := by
  rw [sourceCoupling_eq, lapse_sq]
  unfold gaugeScale
  norm_num [div_pow, mul_pow, spinScale_fourth, spinScale_sq]
  nlinarith [spinScale_sq]

theorem coframe_spatial_balance :
    -(gaugeScale ^ 4 / (4 * sourceCoupling * lapse)) +
      2 * lapse * (spinScale - gaugeScale) * spinScale = lapse * (3 - spinScale ^ 2) := by
  have nonzero := ne_of_gt lapse_pos
  apply (mul_right_cancel₀ nonzero)
  field_simp
  rw [sourceCoupling_eq]
  have square := lapse_sq
  unfold gaugeScale
  nlinarith [spinScale_sq, sq_nonneg (spinScale ^ 2 - 2)]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
