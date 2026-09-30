import H0mework.NavierStokes.WindowPhysics.HeatMultiplier

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal Topology

namespace SaturationMonoid.NavierStokes.NativeHeatSpatialSynthesis

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeFullOrderAction NativeFullOrderSynthesis NativeEndpointVelocityCarrier NativePhysicalContinuous
open NativeUnifiedHeatAction NativeHeatSpatialMultiplier

noncomputable section

def velocityMoment (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag) (order : ℕ) :
    WholeRestartVelocityEndpointState →L[ℝ] WholeRestartVelocityEndpointState :=
  momentCLM nu lag positive order Subtype.val

theorem velocityMoment_row (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag) (order : ℕ)
    (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    wholeVelocity (velocityMoment nu lag positive order value) wave =
      frequencySize wave ^ order • wholeVelocity (heatCLM nu lag value) wave := by
  by_cases zero : wave = 0
  · subst wave
    simp
  · funext coordinate
    rw [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave, zero⟩,
      wholeVelocity_nonzero _ ⟨wave, zero⟩, heatCLM_row]
    change ((frequencySize wave ^ order * finiteStateVorticityHeatMultiplier nu.coeff lag wave) • value ⟨wave, zero⟩) coordinate = _
    rw [PiLp.smul_apply, PiLp.smul_apply, mul_smul]

theorem velocityMoment_density (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag) (order : ℕ)
    (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (wholeVelocity (heatCLM nu lag value) wave) =
      vorticityRowAmplitude (wholeVelocity (velocityMoment nu lag positive order value)) wave ^ 2 := by
  rw [vorticityRowAmplitude_sq, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    velocityMoment_row]
  simp only [complexCoordinateAmplitudeSq, Pi.smul_apply, Complex.real_smul,
    Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
  rw [two_mul, pow_add]

theorem velocity_square_summable (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (value : WholeRestartVelocityEndpointState) (order : ℕ) :
    Summable fun wave => frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (wholeVelocity (heatCLM nu lag value) wave) := by
  simp_rw [velocityMoment_density nu lag positive]
  exact summable_vorticityRowAmplitude_sq _

theorem velocity_square_bound (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (value : WholeRestartVelocityEndpointState) (order : ℕ) :
    (∑' wave, frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (wholeVelocity (heatCLM nu lag value) wave)) ≤
      budget nu lag order ^ 2 * ‖value‖ ^ 2 := by
  simp_rw [velocityMoment_density nu lag positive]
  change wholeVorticityEuclideanMass (wholeVelocity (velocityMoment nu lag positive order value)) ≤ _
  rw [wholeVelocity_mass, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (momentCLM_bound nu lag positive order Subtype.val value) 2

theorem velocity_smooth (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (value : WholeRestartVelocityEndpointState) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField (wholeVelocity (heatCLM nu lag value))) :=
  spatialField_smooth_of_square _ (velocity_square_summable nu lag positive value)

theorem velocity_derivative_bound (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (value : WholeRestartVelocityEndpointState) (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (spatialField (wholeVelocity (heatCLM nu lag value))) point‖ ≤
      (2 * Real.pi) ^ order *
        ((budget nu lag (order + 2) ^ 2 * ‖value‖ ^ 2 + ∑' wave, decay wave) / 2) := by
  apply (spatialField_bound_of_square _ (velocity_square_summable nu lag positive value) order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div_of_nonneg_right (add_le_add (velocity_square_bound nu lag positive value (order + 2)) le_rfl)
    (by norm_num)

theorem stress_weight_inverse_le (wave : IntegerWavevector) :
    (NativeCompleteStressCarrier.weight wave)⁻¹ ≤ frequencySize wave ^ 2 := by
  by_cases zero : wave = 0
  · subst wave
    simp [NativeCompleteStressCarrier.weight, frequencySize]
  · simpa only [NativeCompleteStressCarrier.weight, if_neg zero, inv_inv] using normSq_le_frequencySize_sq wave

def stressTensor (nu : Viscosity) (lag : ℝ≥0) (value : NativeCompleteStressCarrier.Space)
    (wave : IntegerWavevector) : NativeCompleteStressCarrier.Tensor :=
  (finiteStateVorticityHeatMultiplier nu.coeff lag wave * (NativeCompleteStressCarrier.weight wave)⁻¹) • value wave

theorem stressTensor_row (nu : Viscosity) (lag : ℝ≥0) (value : NativeCompleteStressCarrier.Space)
    (wave : IntegerWavevector) (output input : Coordinate) :
    stressTensor nu lag value wave (output, input) =
      finiteStateVorticityHeatMultiplier nu.coeff lag wave •
        NativeCompleteStressCarrier.read value wave output input := by
  change (finiteStateVorticityHeatMultiplier nu.coeff lag wave * (NativeCompleteStressCarrier.weight wave)⁻¹) •
    value wave (output, input) = _
  rw [mul_smul]
  rfl

theorem stress_density_le (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (value : NativeCompleteStressCarrier.Space) (order : ℕ) (wave : IntegerWavevector) :
    frequencySize wave ^ (2 * order) * ‖stressTensor nu lag value wave‖ ^ 2 ≤
      ‖momentCLM nu lag positive (order + 2) id value wave‖ ^ 2 := by
  have multiplier := mul_le_mul_of_nonneg_left (stress_weight_inverse_le wave)
    (mul_nonneg (pow_nonneg (frequencySize_nonneg wave) order)
      (finiteStateVorticityHeatMultiplier_nonneg nu.coeff lag wave))
  have ordered : frequencySize wave ^ order *
      (finiteStateVorticityHeatMultiplier nu.coeff lag wave * (NativeCompleteStressCarrier.weight wave)⁻¹) ≤
      frequencySize wave ^ (order + 2) * finiteStateVorticityHeatMultiplier nu.coeff lag wave := by
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using multiplier
  have scalarNonneg : 0 ≤ finiteStateVorticityHeatMultiplier nu.coeff lag wave *
      (NativeCompleteStressCarrier.weight wave)⁻¹ := by
    exact mul_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _) (inv_nonneg.mpr (NativeCompleteStressCarrier.weight_pos wave).le)
  rw [momentCLM_row, stressTensor, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [id_eq]
  rw [
    abs_of_nonneg scalarNonneg, abs_of_nonneg (mul_nonneg (pow_nonneg (frequencySize_nonneg wave) _)
      (finiteStateVorticityHeatMultiplier_nonneg _ _ _))]
  rw [Nat.mul_comm 2 order, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀
    (mul_nonneg (pow_nonneg (frequencySize_nonneg wave) _) (mul_nonneg scalarNonneg (norm_nonneg _)))
    (by nlinarith [norm_nonneg (value wave)]) 2

theorem stress_square_summable (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (value : NativeCompleteStressCarrier.Space) (order : ℕ) :
    Summable fun wave => frequencySize wave ^ (2 * order) * ‖stressTensor nu lag value wave‖ ^ 2 := by
  have generated : Summable fun wave => ‖momentCLM nu lag positive (order + 2) id value wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (momentCLM nu lag positive (order + 2) id value)).summable
  exact generated.of_nonneg_of_le (fun wave => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) _) (sq_nonneg _))
    (stress_density_le nu lag positive value order)

theorem stress_square_bound (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (value : NativeCompleteStressCarrier.Space) (order : ℕ) :
    (∑' wave, frequencySize wave ^ (2 * order) * ‖stressTensor nu lag value wave‖ ^ 2) ≤
      budget nu lag (order + 2) ^ 2 * ‖value‖ ^ 2 := by
  have generated : HasSum (fun wave => ‖momentCLM nu lag positive (order + 2) id value wave‖ ^ 2)
      (‖momentCLM nu lag positive (order + 2) id value‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (momentCLM nu lag positive (order + 2) id value)
  apply ((stress_square_summable nu lag positive value order).tsum_le_tsum
    (stress_density_le nu lag positive value order) generated.summable).trans
  rw [generated.tsum_eq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (momentCLM_bound nu lag positive (order + 2) id value) 2

end
end SaturationMonoid.NavierStokes.NativeHeatSpatialSynthesis
