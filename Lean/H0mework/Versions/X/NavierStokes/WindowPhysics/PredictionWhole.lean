import H0mework.Versions.X.NavierStokes.WindowPhysics.PredictionRows

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewPrediction

open Set Filter MeasureTheory
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

def forcingBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  ‖divergenceCLM‖ * NativeUnifiedCompleteSource.budget seed

theorem forcing_bound (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    ‖forcing seed lag time‖ ≤ forcingBudget seed := by
  have bounded : ‖source seed lag time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (NativeCompleteHeatTransport.fullHeat_bound nu lag _).trans
      (NativeForwardWindowSource.source_bound seed time)
  exact (divergenceCLM.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((WithLp.norm_snd_le _ _).trans bounded) (norm_nonneg _))

def heatForcing (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (target time : ℝ) :
    WholeRestartVelocityEndpointState :=
  heatCLM nu ⟨max (target - time) 0, le_max_right _ _⟩ (forcing seed lag time)

theorem heatForcing_row (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (target time : ℝ) (wave : NonzeroIntegerWavevector) :
    heatForcing seed lag target time wave =
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave.1) * max (target - time) 0) •
        forcingRow seed lag wave time := heatCLM_row nu _ _ wave

theorem heatForcing_bound (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (target time : ℝ) :
    ‖heatForcing seed lag target time‖ ≤ forcingBudget seed :=
  (heat_bound nu _ _).trans (forcing_bound seed lag time)

theorem heatForcing_measurable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (target : ℝ) :
    AEStronglyMeasurable (heatForcing seed lag target) volume := by
  have coordinate (wave : NonzeroIntegerWavevector) : AEStronglyMeasurable
      (fun time => heatForcing seed lag target time wave) volume := by
    simp only [heatForcing_row]
    exact ((show Continuous (fun time : ℝ =>
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave.1) * max (target - time) 0)) by fun_prop).smul
        (forcingRow_continuous seed lag wave)).aestronglyMeasurable
  let partialSum (observed : Finset NonzeroIntegerWavevector) (time : ℝ) : WholeRestartVelocityEndpointState :=
    ∑ wave ∈ observed, lp.single 2 wave (heatForcing seed lag target time wave)
  have measurable (observed : Finset NonzeroIntegerWavevector) : AEStronglyMeasurable (partialSum observed) volume := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
      |>.comp_aestronglyMeasurable (coordinate wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset NonzeroIntegerWavevector)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (heatForcing seed lag target time)

theorem heatForcing_integrable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (target first last : ℝ) :
    IntervalIntegrable (heatForcing seed lag target) volume first last := by
  rw [intervalIntegrable_iff']
  exact IntegrableOn.of_bound (isCompact_uIcc.measure_lt_top (μ := volume))
    (heatForcing_measurable seed lag target).restrict (forcingBudget seed)
    (Eventually.of_forall (heatForcing_bound seed lag target))

/-- Future mean values do not enter the Duhamel input: only the prepared state and the generated stress do. -/
def prediction (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (first last : ℝ) :
    WholeRestartVelocityEndpointState :=
  heatCLM nu ⟨max (last - first) 0, le_max_right _ _⟩ (state seed lag first) +
    ∫ time in first..last, heatForcing seed lag last time

theorem source_prediction (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (first last : ℝ) (valid : -1 < first) (ordered : first ≤ last) :
    state seed lag last = prediction seed lag first last := by
  apply lp.ext
  funext wave
  have projected := (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).intervalIntegral_comp_comm
    (heatForcing_integrable seed lag last first last)
  change (∫ time in first..last, heatForcing seed lag last time wave) =
    (∫ time in first..last, heatForcing seed lag last time) wave at projected
  change row seed lag wave last =
    heatCLM nu ⟨max (last - first) 0, le_max_right _ _⟩ (state seed lag first) wave +
      (∫ time in first..last, heatForcing seed lag last time) wave
  erw [heatCLM_row]
  change row seed lag wave last =
    Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave.1) * max (last - first) 0) • row seed lag wave first +
      (∫ time in first..last, heatForcing seed lag last time) wave
  rw [max_eq_left (sub_nonneg.mpr ordered), ← projected, row_duhamel seed lag wave first last valid ordered]
  congr 1
  apply intervalIntegral.integral_congr
  intro time inside
  rw [uIcc_of_le ordered] at inside
  dsimp only
  rw [heatForcing_row, max_eq_left (sub_nonneg.mpr inside.2)]

theorem prediction_initial (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (first : ℝ) :
    prediction seed lag first first = state seed lag first := by
  simp only [prediction, sub_self, max_self, intervalIntegral.integral_same, add_zero]
  change heatCLM nu 0 _ = _
  rw [heatCLM_zero, ContinuousLinearMap.id_apply]

theorem prediction_physical (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (first last : ℝ) (valid : -1 < first) (ordered : first ≤ last) :
    NativeNegativeFourMomentum.embed (source seed lag last).fst = prediction seed lag first last := by
  rw [← state_embedded]
  exact source_prediction seed lag first last valid ordered

theorem prediction_physical_unique (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (first last : ℝ) (valid : -1 < first) (ordered : first ≤ last)
    (value : WholeRestartVelocityEndpointState)
    (predicted : NativeNegativeFourMomentum.embed value = prediction seed lag first last) :
    value = (source seed lag last).fst := by
  apply NativeNegativeFourMomentum.embed_injective
  exact predicted.trans (prediction_physical seed lag first last valid ordered).symm

end
end SaturationMonoid.NavierStokes.NativeViewPrediction
