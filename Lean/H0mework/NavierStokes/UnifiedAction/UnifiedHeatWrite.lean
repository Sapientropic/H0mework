import H0mework.NavierStokes.UnifiedAction.UnifiedHeatAction
import H0mework.NavierStokes.UnifiedAction.UnifiedGlobalDuhamel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedHeatWrite

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open NativeCompleteStressCarrier NativeCompleteStressAction NativeUnifiedHeatAction NativeTimeJetCarrier

noncomputable section

variable {nu : Viscosity}

def forcingCLM : FullSpace →L[ℝ] WholeRestartVelocityEndpointState :=
  divergenceCLM.comp (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space)

def forcing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState :=
  forcingCLM (NativeUnifiedCompleteSource.source seed time)

theorem forcing_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : NonzeroIntegerWavevector) :
    forcing seed time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (projectedDivergenceCLM wave.1 (NativeUnifiedGlobalStressSource.stress seed time wave.1)) :=
  divergenceCLM_source _ _ (NativeUnifiedGlobalStressSource.stress_bound seed time) wave

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  ‖forcingCLM‖ * NativeUnifiedCompleteSource.budget seed

theorem forcing_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖forcing seed time‖ ≤ budget seed :=
  (forcingCLM.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (NativeUnifiedCompleteSource.source_bound seed time) (norm_nonneg _))

theorem forcing_measurable (seed : GeneratedWholeRestartCurrent nu) : AEStronglyMeasurable (forcing seed) volume :=
  forcingCLM.continuous.comp_aestronglyMeasurable (NativeUnifiedCompleteSource.source_measurable seed)

/-- On the causal integration interval the duration is exactly `target - sample`. -/
def heatForcing (seed : GeneratedWholeRestartCurrent nu) (target sample : ℝ) : WholeRestartVelocityEndpointState :=
  heatCLM nu ⟨max (target - sample) 0, le_max_right _ _⟩ (forcing seed sample)

theorem heatForcing_row (seed : GeneratedWholeRestartCurrent nu) (target sample : ℝ) (wave : NonzeroIntegerWavevector) :
    heatForcing seed target sample wave =
      Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave.1) * max (target - sample) 0) • forcing seed sample wave :=
  heatCLM_row nu _ _ wave

theorem heatForcing_bound (seed : GeneratedWholeRestartCurrent nu) (target sample : ℝ) :
    ‖heatForcing seed target sample‖ ≤ budget seed :=
  (heat_bound nu _ _).trans (forcing_bound seed sample)

theorem heatForcing_measurable (seed : GeneratedWholeRestartCurrent nu) (target : ℝ) :
    AEStronglyMeasurable (heatForcing seed target) volume := by
  have coordinate (wave : NonzeroIntegerWavevector) : AEStronglyMeasurable
      (fun sample => heatForcing seed target sample wave) volume := by
    simp only [heatForcing_row]
    have scalar : Continuous fun sample : ℝ =>
        Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave.1) * max (target - sample) 0) := by fun_prop
    exact scalar.aestronglyMeasurable.smul
      ((lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
        |>.comp_aestronglyMeasurable (forcing_measurable seed))
  let partialSum (observed : Finset NonzeroIntegerWavevector) (time : ℝ) : WholeRestartVelocityEndpointState :=
    ∑ wave ∈ observed, lp.single 2 wave (heatForcing seed target time wave)
  have measurable (observed : Finset NonzeroIntegerWavevector) : AEStronglyMeasurable (partialSum observed) volume := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
      |>.comp_aestronglyMeasurable (coordinate wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset NonzeroIntegerWavevector)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (heatForcing seed target time)

theorem heatForcing_integrable (seed : GeneratedWholeRestartCurrent nu) (target a b : ℝ) :
    IntervalIntegrable (heatForcing seed target) volume a b := by
  rw [intervalIntegrable_iff']
  exact IntegrableOn.of_bound (isCompact_uIcc.measure_lt_top (μ := volume))
    (heatForcing_measurable seed target).restrict (budget seed)
    (Eventually.of_forall (heatForcing_bound seed target))

theorem source_duhamel (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    NativeGlobalHilbertAction.sourceState seed b =
      heatCLM nu ⟨b - a, sub_nonneg.mpr ordered⟩ (NativeGlobalHilbertAction.sourceState seed a) +
        ∫ time in a..b, heatForcing seed b time := by
  apply lp.ext
  funext wave
  have rawIntegrable : IntervalIntegrable (fun time =>
      Real.exp (-NativeUnifiedGlobalDuhamel.damping nu wave.1 * (b - time)) •
        NativeUnifiedGlobalDuhamel.forcing seed wave.1 time) volume a b :=
    (NativeUnifiedGlobalDuhamel.forcing_integrable seed wave a b a_nonnegative ordered).continuousOn_smul (by fun_prop)
  have evaluation := (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).intervalIntegral_comp_comm
    (heatForcing_integrable seed b a b)
  have wholeIntegral : (∫ time in a..b, heatForcing seed b time) wave =
      NativeNegativeFourMomentum.weightedRowCLM wave.1
        (∫ time in a..b, Real.exp (-NativeUnifiedGlobalDuhamel.damping nu wave.1 * (b - time)) •
          NativeUnifiedGlobalDuhamel.forcing seed wave.1 time) := by
    change (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)
      (∫ time in a..b, heatForcing seed b time) = _
    rw [← evaluation, ← (NativeNegativeFourMomentum.weightedRowCLM wave.1).intervalIntegral_comp_comm rawIntegrable]
    change (∫ time in a..b, heatForcing seed b time wave) = _
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le ordered] at inside
    change heatForcing seed b time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (Real.exp (-NativeUnifiedGlobalDuhamel.damping nu wave.1 * (b - time)) •
        NativeUnifiedGlobalDuhamel.forcing seed wave.1 time)
    have heatRow := heatForcing_row seed b time wave
    rw [heatRow, max_eq_left (sub_nonneg.mpr inside.2), forcing_row seed time wave, map_smul]
    rfl
  have readVelocity (time : ℝ) : NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeUnifiedGlobalDuhamel.velocity seed wave.1 time) = NativeGlobalHilbertAction.sourceState seed time wave :=
    NativeNegativeFourMomentum.weightedRowCLM_row (NativeAbsoluteEventualControl.velocity seed time) wave
  have heatRow := heatCLM_row nu ⟨b - a, sub_nonneg.mpr ordered⟩ (NativeGlobalHilbertAction.sourceState seed a) wave
  change NativeGlobalHilbertAction.sourceState seed b wave =
    heatCLM nu ⟨b - a, sub_nonneg.mpr ordered⟩ (NativeGlobalHilbertAction.sourceState seed a) wave +
      (∫ time in a..b, heatForcing seed b time) wave
  rw [heatRow, wholeIntegral, ← readVelocity b, ← readVelocity a]
  have original := congrArg (NativeNegativeFourMomentum.weightedRowCLM wave.1)
    (NativeUnifiedGlobalDuhamel.source_duhamel_nonzero seed wave a b a_nonnegative ordered)
  simp only [map_add, map_smul, NativeUnifiedGlobalDuhamel.damping] at original
  convert! original using 1

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem heatForcing_generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (target sample : ℝ) (nonnegative : 0 ≤ sample) :
    heatForcing seed (response.2.clockAdvance + target) (response.2.clockAdvance + sample) =
      heatForcing response.1 target sample := by
  have actual := congrArg forcingCLM
    (NativeUnifiedCompleteSource.source_generated_next seed response generated sample nonnegative)
  change forcing seed (response.2.clockAdvance + sample) = forcing response.1 sample at actual
  unfold heatForcing
  rw [actual]
  apply congrArg (fun duration : ℝ≥0 => heatCLM nu duration (forcing response.1 sample))
  apply Subtype.ext
  simp only [add_sub_add_left_eq_sub]

theorem source_generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) :
    NativeGlobalHilbertAction.sourceState response.1 0 =
      heatCLM nu ⟨response.2.clockAdvance, response.2.clockAdvance_pos.le⟩ (NativeGlobalHilbertAction.sourceState seed 0) +
        ∫ time in (0 : ℝ)..response.2.clockAdvance, heatForcing seed response.2.clockAdvance time := by
  have source := source_duhamel seed 0 response.2.clockAdvance le_rfl response.2.clockAdvance_pos.le
  have same := NativeFiniteMacroEvolution.source_generated_next_evolution response generated 0 le_rfl
  simp only [add_zero] at same
  simpa only [sub_zero, NativeGlobalHilbertAction.sourceState, same] using source

end
end SaturationMonoid.NavierStokes.NativeUnifiedHeatWrite
