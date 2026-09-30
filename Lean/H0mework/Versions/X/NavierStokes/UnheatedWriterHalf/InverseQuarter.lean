import H0mework.Versions.X.NavierStokes.UnheatedWriterHalf.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedInverseQuarter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeWholeH1Pairing
open NativeUnheatedHalfNonlinear NativeUnheatedPairNegativeKernel
noncomputable section

theorem quarter_positive (wave : IntegerWavevector) (nonzero : wave ≠ 0) : 0 < quarter wave :=
  Real.sqrt_pos.mpr (root_positive wave nonzero)

theorem inverse_bound (wave : Wave) : (quarter wave.1)⁻¹ ≤ 1 := by
  have multiplier : 1 ≤ integerWaveViscousMultiplier wave.1 := by
    calc
      (1 : ℝ) ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
      _ = (2*Real.pi)^2*1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_integerWaveNormSq wave.1 wave.2) (sq_nonneg _)
  have first : 1 ≤ root wave.1 := Real.le_sqrt_of_sq_le (by simpa only [one_pow] using multiplier)
  exact inv_le_one_of_one_le₀ (Real.le_sqrt_of_sq_le (by simpa only [one_pow] using first))

def inverseQuarter : State →L[ℝ] State :=
  lp.mapCLM 2 (fun wave : Wave => (quarter wave.1)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ Coordinate))
    zero_le_one (fun wave => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro value
      change ‖(quarter wave.1)⁻¹ • value‖ ≤ 1*‖value‖
      rw [one_mul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (quarter_nonnegative _))]
      exact mul_le_of_le_one_left (norm_nonneg _) (inverse_bound wave))

theorem inverseQuarter_row (value : State) (wave : Wave) :
    inverseQuarter value wave = (quarter wave.1)⁻¹ • value wave := rfl

theorem inverseQuarter_bound (value : State) : ‖inverseQuarter value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  rw [inverseQuarter_row, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (quarter_nonnegative _))]
  exact mul_le_of_le_one_left (norm_nonneg _) (inverse_bound wave)

theorem whole_row (value : State) (wave : IntegerWavevector) :
    wholeVelocity (inverseQuarter value) wave = (quarter wave)⁻¹ • wholeVelocity value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp only [wholeVelocity_zero, smul_zero]
  · funext coordinate
    rw [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave,zero⟩, wholeVelocity_nonzero _ ⟨wave,zero⟩,
      inverseQuarter_row, PiLp.smul_apply]

theorem restore (value : State) (wave : IntegerWavevector) :
    quarter wave • wholeVelocity (inverseQuarter value) wave = wholeVelocity value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp only [wholeVelocity_zero, smul_zero]
  · rw [whole_row]
    exact smul_inv_smul₀ (quarter_positive wave zero).ne' _

end
end SaturationMonoid.NavierStokes.NativeUnheatedInverseQuarter
