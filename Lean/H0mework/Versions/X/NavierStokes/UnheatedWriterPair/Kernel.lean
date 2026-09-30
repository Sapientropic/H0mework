import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.Evolution

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairInverseKernel

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeCompleteStressCarrier NativeUnheatedStressPairEvolution

noncomputable section
variable {nu : Viscosity}

def scale (nu : Viscosity) : ℝ := nu.coeff * (2 * Real.pi) ^ 2 / 2

theorem scale_positive : 0 < scale nu := by
  unfold scale
  positivity [nu.coeff_pos]

theorem decay_floor (first last : IntegerWavevector) (nonzero : first ≠ 0 ∨ last ≠ 0) :
    nu.coeff * (2 * Real.pi) ^ 2 ≤ decay nu first last := by
  have lower : 1 ≤ integerWaveNormSq first + integerWaveNormSq last := by
    rcases nonzero with left | right
    · linarith [one_le_integerWaveNormSq first left, integerWaveNormSq_nonneg last]
    · linarith [one_le_integerWaveNormSq last right, integerWaveNormSq_nonneg first]
  have multiplied := mul_le_mul_of_nonneg_left lower
    (mul_nonneg nu.coeff_pos.le (sq_nonneg (2 * Real.pi)))
  simpa only [mul_one, decay, integerWaveViscousMultiplier, mul_add, mul_assoc] using multiplied

theorem decay_coercive (first last : IntegerWavevector) (nonzero : first ≠ 0 ∨ last ≠ 0) :
    scale nu * (weight (first + last))⁻¹ ≤ decay nu first last := by
  by_cases zero : first + last = 0
  · simp only [weight, if_pos zero, inv_one, mul_one]
    have floor := decay_floor (nu := nu) first last nonzero
    have positive := scale_positive (nu := nu)
    unfold scale at positive ⊢
    linarith
  · simp only [weight, if_neg zero, inv_inv]
    have original := output_decay (nu := nu) first last
    unfold integerWaveViscousMultiplier at original
    unfold scale
    nlinarith

theorem inverse_bound (first last : IntegerWavevector) :
    (decay nu first last)⁻¹ ≤ (scale nu)⁻¹ * weight (first + last) := by
  by_cases nonzero : first ≠ 0 ∨ last ≠ 0
  · have lower := decay_coercive (nu := nu) first last nonzero
    have positive : 0 < scale nu * (weight (first + last))⁻¹ :=
      mul_pos scale_positive (inv_pos.mpr (weight_pos _))
    have bounded := one_div_le_one_div_of_le positive lower
    simpa only [one_div, mul_inv_rev, inv_inv, mul_comm] using bounded
  · push Not at nonzero
    rcases nonzero with ⟨rfl, rfl⟩
    simp only [decay, integerWaveViscousMultiplier, integerWaveNormSq, Pi.zero_apply,
      Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero,
      add_zero, inv_zero]
    exact mul_nonneg (inv_nonneg.mpr scale_positive.le) (weight_pos _).le

theorem inverse_power_bound (order : ℕ) (first last : IntegerWavevector) :
    ((decay nu first last)⁻¹) ^ order ≤ (scale nu)⁻¹ ^ order * weight (first + last) ^ order := by
  rw [← mul_pow]
  apply pow_le_pow_left₀
  · exact inv_nonneg.mpr (by
      unfold decay integerWaveViscousMultiplier
      positivity [nu.coeff_pos, integerWaveNormSq_nonneg first, integerWaveNormSq_nonneg last])
  · exact inverse_bound first last

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairInverseKernel
