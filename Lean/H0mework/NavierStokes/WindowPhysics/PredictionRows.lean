import H0mework.NavierStokes.WindowPhysics.HeatEvolution
import H0mework.NavierStokes.UnifiedAction.UnifiedHeatWrite

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewPrediction

open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open NativeCompleteStressAction NativeWindowHeatEvolution NativeUnifiedHeatAction

noncomputable section

variable {nu : Viscosity}

/-- The predictive input is the generated complete stress, independently of the future mean readout. -/
def forcing (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    WholeRestartVelocityEndpointState := divergenceCLM (source seed lag time).snd

def row (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (wave : NonzeroIntegerWavevector) (time : ℝ) := state seed lag time wave

def forcingRow (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (wave : NonzeroIntegerWavevector) (time : ℝ) := forcing seed lag time wave

theorem viscous_embedded (value : WholeRestartVelocityEndpointState) (wave : NonzeroIntegerWavevector) :
    viscousCLM nu value wave =
      (nu.coeff * integerWaveViscousMultiplier wave.1) • NativeNegativeFourMomentum.embed value wave := by
  have original := NativeNegativeFourMomentum.weightedRowCLM_row value wave
  change NativeNegativeFourMomentum.weightedRowCLM wave.1
    (NativeEndpointVelocityCarrier.wholeVelocity value wave.1) = NativeNegativeFourMomentum.embed value wave at original
  rw [viscousCLM_source, map_smul, original]

theorem row_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (wave : NonzeroIntegerWavevector) (time : ℝ) (valid : -1 < time) :
    HasDerivAt (row seed lag wave)
      (forcingRow seed lag wave time -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • row seed lag wave time) time := by
  have actual := (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).hasFDerivAt.comp_hasDerivAt time
    (state_hasDerivAt seed lag time valid)
  change HasDerivAt (row seed lag wave)
    (divergenceCLM (source seed lag time).snd wave - viscousCLM nu (source seed lag time).fst wave) time at actual
  rw [viscous_embedded, ← state_embedded] at actual
  exact actual

theorem forcing_continuous (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) :
    Continuous (forcing seed lag) :=
  divergenceCLM.continuous.comp
    ((WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space).continuous.comp
      (source_smooth seed lag).continuous)

theorem forcingRow_continuous (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (wave : NonzeroIntegerWavevector) : Continuous (forcingRow seed lag wave) :=
  (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous.comp
    (forcing_continuous seed lag)

theorem row_duhamel (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (wave : NonzeroIntegerWavevector) (first last : ℝ) (valid : -1 < first) (ordered : first ≤ last) :
    row seed lag wave last =
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave.1) * (last - first)) • row seed lag wave first +
        ∫ time in first..last,
          Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave.1) * (last - time)) • forcingRow seed lag wave time := by
  let damping := nu.coeff * integerWaveViscousMultiplier wave.1
  let factor (time : ℝ) := Real.exp (damping * (time - first))
  have factorDerivative (time : ℝ) : HasDerivAt factor (factor time * damping) time := by
    simpa only [factor, id_eq, mul_one] using (((hasDerivAt_id time).sub_const first).const_mul damping).exp
  have productDerivative (time : ℝ) (inside : time ∈ uIcc first last) :
      HasDerivAt (fun sample => factor sample • row seed lag wave sample)
        (factor time • forcingRow seed lag wave time) time := by
    rw [uIcc_of_le ordered] at inside
    have actual := (factorDerivative time).fun_smul
      (row_hasDerivAt seed lag wave time (valid.trans_le inside.1))
    simpa only [damping, smul_sub, smul_smul, sub_add_cancel] using actual
  have integrable : IntervalIntegrable (fun time => factor time • forcingRow seed lag wave time) volume first last :=
    ((show Continuous factor by fun_prop).smul (forcingRow_continuous seed lag wave)).intervalIntegrable first last
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt productDerivative integrable
  have start : factor first = 1 := by simp [factor]
  rw [start, one_smul] at written
  have primitive : row seed lag wave first +
      (∫ time in first..last, factor time • forcingRow seed lag wave time) = factor last • row seed lag wave last := by
    rw [written]
    abel
  have weighted := congrArg (fun value => Real.exp (-damping * (last - first)) • value) primitive
  rw [smul_add, ← intervalIntegral.integral_smul, smul_smul] at weighted
  have cancel : Real.exp (-damping * (last - first)) * factor last = 1 := by
    dsimp only [factor]
    rw [← Real.exp_add, show -damping * (last - first) + damping * (last - first) = 0 by ring,
      Real.exp_zero]
  rw [cancel, one_smul] at weighted
  rw [← weighted]
  congr 1
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only [factor]
  rw [smul_smul, ← Real.exp_add]
  congr 2
  dsimp only [damping]
  ring

end
end SaturationMonoid.NavierStokes.NativeViewPrediction
