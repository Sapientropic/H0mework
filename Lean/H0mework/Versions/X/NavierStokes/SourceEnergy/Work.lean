import H0mework.Versions.X.NavierStokes.SourceEnergy.Evolution
import H0mework.Versions.X.NavierStokes.SourceSpacetime.Curl

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewEnergyWork

open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeTimeJetCarrier
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeWindowHeatEvolution
open NativeViewEnergyContent NativeViewEnergyEvolution NativeViewPhysicalCurl
open NativeWholeH1Mixed NativeWholeH1Pairing NativeCompleteHeatTransport

noncomputable section

variable {nu : Viscosity}

def residualRow (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ)
    (wave : NonzeroIntegerWavevector) : ComplexCoordinateEuclidean :=
  euclideanCLM (projectedDivergenceCLM wave.1 (NativeCompleteStressCarrier.read (residualValue (source seed lag time)) wave.1))

def residualWork (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  ∑' wave : NonzeroIntegerWavevector, inner ℝ (residualRow seed lag time wave) ((source seed lag time).fst wave)

def dissipation (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  ∑' wave : NonzeroIntegerWavevector, integerWaveViscousMultiplier wave.1 * ‖(source seed lag time).fst wave‖ ^ 2

theorem dissipation_nonnegative (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    0 ≤ dissipation seed lag time :=
  tsum_nonneg fun wave => mul_nonneg (multiplier_positive wave).le (sq_nonneg _)

/-- This is the complete residual stress action before any pairing is taken. -/
theorem residual_action (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    divergenceCLM (residualValue (source seed lag time)) = momentumCLM nu (source seed lag time) -
      (divergenceCLM (NativeCompleteStressBilinear.mixed (wholeVelocity (source seed lag time).fst)
        (wholeVelocity (source seed lag time).fst)) - viscousCLM nu (source seed lag time).fst) := by
  change divergenceCLM ((source seed lag time).snd - _) =
    (divergenceCLM (source seed lag time).snd - viscousCLM nu (source seed lag time).fst) -
      (divergenceCLM _ - viscousCLM nu (source seed lag time).fst)
  rw [map_sub]
  abel

theorem momentum_rate_row (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ)
    (valid : -1 < time) (wave : NonzeroIntegerWavevector) :
    velocityJet seed lag 1 time wave =
      euclideanCLM (projectedDivergenceCLM wave.1 (NativeCompleteStressCarrier.read (source seed lag time).snd wave.1)) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • (source seed lag time).fst wave := by
  have actual := congrArg (fun value => integerWaveNormSq wave.1 ^ 2 • value wave) (momentum_rate seed lag time valid)
  rw [NativeNegativeFourMomentum.embed_reconstruct, NativeCompleteActionOperator.momentum_complete_row,
    NativeCompleteFilteredWrite.decode_weighted_row] at actual
  rw [actual]
  change euclideanCLM (_ - _ • _) = _
  rw [map_sub, map_smul]
  congr 2
  apply PiLp.ext
  intro coordinate
  exact wholeVelocity_nonzero _ wave coordinate

def residualNegative (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 ≤ time) : WholeRestartVelocityEndpointState :=
  inverseGradient (velocityJet seed lag 1 time) +
    nu.coeff • gradientValue (sourcePhysical seed lag time valid) (sourcePhysical_H1 seed lag positive time valid) -
    negativeAction (sourcePhysical seed lag time valid) (sourcePhysical seed lag time valid)
      (sourcePhysical_H1 seed lag positive time valid) (sourcePhysical_H1 seed lag positive time valid)

theorem residualNegative_row (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) (wave : NonzeroIntegerWavevector) :
    residualNegative seed lag positive time valid.le wave =
      (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • residualRow seed lag time wave := by
  have scale : (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ *
      (nu.coeff * integerWaveViscousMultiplier wave.1) =
      nu.coeff * Real.sqrt (integerWaveViscousMultiplier wave.1) := by
    have square := Real.sq_sqrt (multiplier_positive wave).le
    have nonzero := (Real.sqrt_pos.mpr (multiplier_positive wave)).ne'
    field_simp
    rw [square]
    ring
  change (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • velocityJet seed lag 1 time wave +
    nu.coeff • (Real.sqrt (integerWaveViscousMultiplier wave.1) • (source seed lag time).fst wave) -
    (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • euclideanCLM
      (projectedDivergenceCLM wave.1 (NativeHigherTimeJets.mixedFlux (wholeVelocity (source seed lag time).fst)
        (wholeVelocity (source seed lag time).fst) wave.1)) = _
  rw [momentum_rate_row seed lag time valid, residualRow, NativeHeatPairingAverage.residual_read]
  change _ = (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • euclideanCLM
    (projectedDivergenceCLM wave.1 (NativeCompleteStressCarrier.read (source seed lag time).snd wave.1 -
      NativeStressSource.quadraticFlux (wholeVelocity (source seed lag time).fst) wave.1))
  rw [map_sub, map_sub, smul_sub, smul_sub, smul_smul, smul_smul, scale,
    NativeHigherTimeJets.mixedFlux_diagonal]
  abel

theorem residual_pairing_row (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) (wave : NonzeroIntegerWavevector) :
    inner ℝ (residualNegative seed lag positive time valid.le wave)
      (gradientValue (sourcePhysical seed lag time valid.le) (sourcePhysical_H1 seed lag positive time valid.le) wave) =
      inner ℝ (residualRow seed lag time wave) ((source seed lag time).fst wave) := by
  rw [residualNegative_row seed lag positive time valid]
  change inner ℝ (_ • _) (Real.sqrt (integerWaveViscousMultiplier wave.1) • _) = _
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul]
  rfl

theorem residualWork_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) :
    Summable (fun wave : NonzeroIntegerWavevector =>
      inner ℝ (residualRow seed lag time wave) ((source seed lag time).fst wave)) :=
  (lp.summable_inner (𝕜 := ℝ) (residualNegative seed lag positive time valid.le)
    (gradientValue (sourcePhysical seed lag time valid.le) (sourcePhysical_H1 seed lag positive time valid.le))).congr
      (residual_pairing_row seed lag positive time valid)

theorem residualWork_pairing (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) :
    residualWork seed lag time = inner ℝ (residualNegative seed lag positive time valid.le)
      (gradientValue (sourcePhysical seed lag time valid.le) (sourcePhysical_H1 seed lag positive time valid.le)) := by
  rw [lp.inner_eq_tsum]
  exact tsum_congr fun wave => (residual_pairing_row seed lag positive time valid wave).symm

theorem dissipation_gradient (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 ≤ time) :
    dissipation seed lag time = ‖gradientValue (sourcePhysical seed lag time valid)
      (sourcePhysical_H1 seed lag positive time valid)‖ ^ 2 := by
  rw [NativeResolventCompactness.norm_sq_sum]
  apply tsum_congr
  intro wave
  change _ = ‖Real.sqrt (integerWaveViscousMultiplier wave.1) • (source seed lag time).fst wave‖ ^ 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (multiplier_positive wave).le]

theorem energy_balance (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) :
    resolvedRate seed lag time = residualWork seed lag time - nu.coeff * dissipation seed lag time := by
  rw [residualWork_pairing seed lag positive time valid, dissipation_gradient seed lag positive time valid.le,
    residualNegative, inner_sub_left, inner_add_left, real_inner_smul_left,
    inverse_gradient_pairing, real_inner_self_eq_norm_sq,
    NativeWholeH1Cancellation.whole_cancellation nu, sub_zero]
  change inner ℝ (velocityJet seed lag 0 time) (velocityJet seed lag 1 time) =
    inner ℝ (velocityJet seed lag 1 time) ((source seed lag time).fst) + _ - _
  rw [velocity_zero, real_inner_comm]
  ring

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) :
    HasDerivAt (resolved seed lag) (residualWork seed lag time - nu.coeff * dissipation seed lag time) time := by
  rw [← energy_balance seed lag positive time valid]
  exact resolved_hasDerivAt seed lag time

theorem energy_integral (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (first last : ℝ) (first_valid : -1 < first) (last_valid : -1 < last) :
    resolved seed lag last - resolved seed lag first =
      ∫ time in first..last, residualWork seed lag time - nu.coeff * dissipation seed lag time := by
  have within : uIcc first last ⊆ Ioi (-1 : ℝ) :=
    fun _ inside => lt_of_lt_of_le (lt_min first_valid last_valid) inside.1
  have continuous : ContinuousOn (fun time => residualWork seed lag time - nu.coeff * dissipation seed lag time)
      (uIcc first last) := by
    apply (resolvedRate_continuous seed lag).continuousOn.congr
    intro time inside
    exact (energy_balance seed lag positive time (within inside)).symm
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time inside => energy_hasDerivAt seed lag positive time (within inside)) continuous.intervalIntegrable).symm

end
end SaturationMonoid.NavierStokes.NativeViewEnergyWork
