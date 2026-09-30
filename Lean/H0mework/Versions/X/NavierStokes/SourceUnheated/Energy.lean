import H0mework.Versions.X.NavierStokes.SourceUnheated.WindowGradient
import H0mework.Versions.X.NavierStokes.SourceHeat.WindowZero
import H0mework.Versions.X.NavierStokes.SourceEnergy.Work
import H0mework.Versions.X.NavierStokes.StressNegativeOne.Momentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedEnergy
open Set MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeWindowHeatEvolution NativeViewPhysicalCurl
open NativeWholeH1Mixed NativeWholeH1Pairing NativeNegativeOneInclusion NativeViewEnergyContent NativeViewEnergyEvolution
open NativeViewEnergyWork NativeCompleteHeatTransport
noncomputable section
variable {nu : Viscosity}

theorem source_H1 (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    H1 (sourcePhysical seed 0 time valid) := by
  have original := NativeUnheatedWindowGradient.whole_gradient_summable seed 0 time valid
  change Summable (fun wave => integerWaveNormSq wave *
    NativeMovingCriticalProduct.amplitude (wholeVelocity (source seed 0 time).fst) wave ^ 2)
  simp only [NativeMovingCriticalProduct.amplitude, euclideanCoordinateRow_norm_sq, NativeZeroHeatWindow.source_zero]
  simpa only [NativeForwardWindowEvolution.velocityJet, NativeForwardWindowJets.jet_zero] using! original

def residualNegative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    WholeRestartVelocityEndpointState :=
  inverseGradient (velocityJet seed 0 1 time) -
    NativeNegativeOneMomentum.momentum nu (sourcePhysical seed 0 time valid) (source_H1 seed time valid)

theorem residual_lower (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    lowerCLM (residualNegative seed time valid.le) = divergenceCLM (residualValue (source seed 0 time)) := by
  rw [residualNegative, map_sub, lower_inverseGradient, NativeNegativeOneMomentum.momentum, lower_momentum,
    momentum_rate seed 0 time valid]
  exact (residual_action seed 0 time).symm

theorem residualNegative_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (wave : NonzeroIntegerWavevector) :
    residualNegative seed time valid.le wave =
      (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • residualRow seed 0 time wave := by
  apply smul_right_injective ComplexCoordinateEuclidean (lowerWeight_positive wave).ne'
  have original := congrArg (fun value : WholeRestartVelocityEndpointState => value wave) (residual_lower seed time valid)
  change lowerWeight wave • residualNegative seed time valid.le wave = _ at original
  rw [NativeCompleteActionOperator.divergence_complete_row] at original
  change lowerWeight wave • residualNegative seed time valid.le wave =
    NativeNegativeFourMomentum.weight wave.1 • residualRow seed 0 time wave at original
  change lowerWeight wave • residualNegative seed time valid.le wave =
    lowerWeight wave • ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • residualRow seed 0 time wave)
  rw [smul_smul, lowerWeight, mul_right_comm,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul]
  exact original

theorem pairing_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (wave : NonzeroIntegerWavevector) :
    inner ℝ (residualNegative seed time valid.le wave)
      (gradientValue (sourcePhysical seed 0 time valid.le) (source_H1 seed time valid.le) wave) =
        inner ℝ (residualRow seed 0 time wave) ((source seed 0 time).fst wave) := by
  rw [residualNegative_row seed time valid]
  change inner ℝ (_ • _) (Real.sqrt (integerWaveViscousMultiplier wave.1) • _) = _
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul]
  rfl

theorem residualWork_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    Summable (fun wave : NonzeroIntegerWavevector =>
      inner ℝ (residualRow seed 0 time wave) ((source seed 0 time).fst wave)) :=
  (lp.summable_inner (𝕜 := ℝ) (residualNegative seed time valid.le)
    (gradientValue (sourcePhysical seed 0 time valid.le) (source_H1 seed time valid.le))).congr
      (pairing_row seed time valid)

theorem residualWork_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    residualWork seed 0 time = inner ℝ (residualNegative seed time valid.le)
      (gradientValue (sourcePhysical seed 0 time valid.le) (source_H1 seed time valid.le)) := by
  rw [lp.inner_eq_tsum]
  exact tsum_congr (fun wave => (pairing_row seed time valid wave).symm)

theorem dissipation_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    Summable (fun wave : NonzeroIntegerWavevector => integerWaveViscousMultiplier wave.1 *
      ‖(source seed 0 time).fst wave‖ ^ 2) := by
  have paid := curl_summable (sourcePhysical seed 0 time valid) (source_H1 seed time valid)
  exact paid

theorem dissipation_gradient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    dissipation seed 0 time = ‖gradientValue (sourcePhysical seed 0 time valid) (source_H1 seed time valid)‖ ^ 2 := by
  rw [NativeResolventCompactness.norm_sq_sum]
  apply tsum_congr
  intro wave
  change _ = ‖Real.sqrt (integerWaveViscousMultiplier wave.1) • (source seed 0 time).fst wave‖ ^ 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (multiplier_positive wave).le]

theorem energy_balance (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    resolvedRate seed 0 time = residualWork seed 0 time - nu.coeff * dissipation seed 0 time := by
  rw [residualWork_pairing seed time valid, dissipation_gradient seed time valid.le,
    residualNegative, NativeNegativeOneMomentum.momentum, inner_sub_left, inner_sub_left, real_inner_smul_left,
    inverse_gradient_pairing, NativeWholeH1Cancellation.whole_cancellation nu, real_inner_self_eq_norm_sq]
  change inner ℝ (velocityJet seed 0 0 time) (velocityJet seed 0 1 time) =
    inner ℝ (velocityJet seed 0 1 time) ((source seed 0 time).fst) - (0 - _) - _
  rw [velocity_zero, real_inner_comm]
  ring

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    HasDerivAt (resolved seed 0) (residualWork seed 0 time - nu.coeff * dissipation seed 0 time) time := by
  rw [← energy_balance seed time valid]
  exact resolved_hasDerivAt seed 0 time

theorem energy_integral (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ)
    (first_valid : -1 < first) (last_valid : -1 < last) :
    resolved seed 0 last - resolved seed 0 first =
      ∫ time in first..last, residualWork seed 0 time - nu.coeff * dissipation seed 0 time := by
  have within : uIcc first last ⊆ Ioi (-1 : ℝ) :=
    fun _ inside => lt_of_lt_of_le (lt_min first_valid last_valid) inside.1
  have continuous : ContinuousOn (fun time => residualWork seed 0 time - nu.coeff * dissipation seed 0 time)
      (uIcc first last) := by
    apply (resolvedRate_continuous seed 0).continuousOn.congr
    exact fun time inside => (energy_balance seed time (within inside)).symm
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time inside => energy_hasDerivAt seed time (within inside)) continuous.intervalIntegrable).symm

theorem resolved_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    resolved seed 0 time = ‖NativePhysicalFourier.realField
      (wholeVelocity (NativeForwardWindowSource.source seed time).fst)‖ ^ 2 / 2 := by
  rw [resolved_physical, NativeZeroHeatWindow.source_zero]

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    residualWork seed 0 time = ∑' wave : NonzeroIntegerWavevector,
      inner ℝ (euclideanCLM (NativeTimeJetCarrier.projectedDivergenceCLM wave.1
        (NativeCompleteStressCarrier.read (residualValue (NativeForwardWindowSource.source seed time)) wave.1)))
        ((NativeForwardWindowSource.source seed time).fst wave) := by
  simp only [residualWork, residualRow, NativeZeroHeatWindow.source_zero]

theorem physical_integral (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ)
    (first_valid : -1 < first) (last_valid : -1 < last) :
    ‖NativePhysicalFourier.realField (wholeVelocity (NativeForwardWindowSource.source seed last).fst)‖ ^ 2 / 2 -
      ‖NativePhysicalFourier.realField (wholeVelocity (NativeForwardWindowSource.source seed first).fst)‖ ^ 2 / 2 =
        ∫ time in first..last, residualWork seed 0 time - nu.coeff * dissipation seed 0 time := by
  rw [← resolved_original, ← resolved_original]
  exact energy_integral seed first last first_valid last_valid

end
end SaturationMonoid.NavierStokes.NativeUnheatedEnergy
