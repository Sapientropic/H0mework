import H0mework.NavierStokes.Heat.SourceDilation
import H0mework.NavierStokes.Heat.PulseContinuity
import H0mework.NavierStokes.UnifiedAction.UnifiedHeatWrite

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedDilationWrite

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeHeatSourceDilation

noncomputable section

variable {nu : Viscosity}

/-- The input is the complete original stress's projected action at the original sample time. -/
def kernel (seed : GeneratedWholeRestartCurrent nu) (target sample : ℝ) : Ambient :=
  translation (target - sample) (embed nu (NativeUnifiedHeatWrite.forcing seed sample))

theorem kernel_norm (seed : GeneratedWholeRestartCurrent nu) (target sample : ℝ) :
    ‖kernel seed target sample‖ = ‖NativeUnifiedHeatWrite.forcing seed sample‖ := by
  exact (translation (target - sample)).norm_map _ |>.trans ((embed nu).norm_map _)

theorem kernel_measurable (seed : GeneratedWholeRestartCurrent nu) (target : ℝ) :
    AEStronglyMeasurable (kernel seed target) volume := by
  have coordinate (wave : NonzeroIntegerWavevector) :
      AEStronglyMeasurable (fun sample => kernel seed target sample wave) volume := by
    have original := (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
      |>.comp_aestronglyMeasurable (NativeUnifiedHeatWrite.forcing_measurable seed)
    exact NativeHeatPulseContinuity.forced_lift_measurable (rate nu wave) (rate_pos nu wave) target original
  let partialSum (observed : Finset NonzeroIntegerWavevector) (time : ℝ) : Ambient :=
    ∑ wave ∈ observed, lp.single 2 wave (kernel seed target time wave)
  have measurable (observed : Finset NonzeroIntegerWavevector) : AEStronglyMeasurable (partialSum observed) volume := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroIntegerWavevector => Fiber) 2 wave).continuous
      |>.comp_aestronglyMeasurable (coordinate wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset NonzeroIntegerWavevector)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (kernel seed target time)

theorem kernel_integrable (seed : GeneratedWholeRestartCurrent nu) (target a b : ℝ) :
    IntervalIntegrable (kernel seed target) volume a b := by
  rw [intervalIntegrable_iff']
  refine IntegrableOn.of_bound (isCompact_uIcc.measure_lt_top (μ := volume))
    (kernel_measurable seed target).restrict (NativeUnifiedHeatWrite.budget seed) ?_
  exact Eventually.of_forall fun time => (kernel_norm seed target time).le.trans
    (NativeUnifiedHeatWrite.forcing_bound seed time)

theorem kernel_read (seed : GeneratedWholeRestartCurrent nu) (target sample : ℝ) (ordered : sample ≤ target) :
    read nu (kernel seed target sample) = NativeUnifiedHeatWrite.heatForcing seed target sample := by
  have actual := read_translation nu ⟨target - sample, sub_nonneg.mpr ordered⟩
    (NativeUnifiedHeatWrite.forcing seed sample)
  convert! actual using 1
  unfold NativeUnifiedHeatWrite.heatForcing
  congr 2
  apply Subtype.ext
  exact max_eq_left (sub_nonneg.mpr ordered)

def window (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) : Ambient :=
  translation (b - a) (embed nu (NativeGlobalHilbertAction.sourceState seed a)) +
    ∫ sample in a..b, kernel seed b sample

/-- One bounded read recovers the original complete H⁻⁴ Duhamel write. -/
theorem window_read (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    read nu (window seed a b) = NativeGlobalHilbertAction.sourceState seed b := by
  have homogeneous := read_translation nu ⟨b - a, sub_nonneg.mpr ordered⟩
    (NativeGlobalHilbertAction.sourceState seed a)
  have integral := ((read nu).restrictScalars ℝ).intervalIntegral_comp_comm (kernel_integrable seed b a b)
  change (∫ sample in a..b, read nu (kernel seed b sample)) = read nu (∫ sample in a..b, kernel seed b sample) at integral
  have exactKernel : (∫ sample in a..b, read nu (kernel seed b sample)) =
      ∫ sample in a..b, NativeUnifiedHeatWrite.heatForcing seed b sample := by
    apply intervalIntegral.integral_congr
    intro sample inside
    rw [uIcc_of_le ordered] at inside
    exact kernel_read seed b sample inside.2
  calc
    read nu (window seed a b) =
        read nu (translation (b - a) (embed nu (NativeGlobalHilbertAction.sourceState seed a))) +
          read nu (∫ sample in a..b, kernel seed b sample) := (read nu).map_add _ _
    _ = NativeUnifiedHeatAction.heatCLM nu ⟨b - a, sub_nonneg.mpr ordered⟩
          (NativeGlobalHilbertAction.sourceState seed a) +
            ∫ sample in a..b, NativeUnifiedHeatWrite.heatForcing seed b sample :=
      congrArg₂ (fun left right : WholeRestartVelocityEndpointState => left + right)
        homogeneous (integral.symm.trans exactKernel)
    _ = NativeGlobalHilbertAction.sourceState seed b :=
      (NativeUnifiedHeatWrite.source_duhamel seed a b a_nonnegative ordered).symm

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem kernel_generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (target sample : ℝ) (nonnegative : 0 ≤ sample) :
    kernel seed (response.2.clockAdvance + target) (response.2.clockAdvance + sample) =
      kernel response.1 target sample := by
  have actual := congrArg NativeUnifiedHeatWrite.forcingCLM
    (NativeUnifiedCompleteSource.source_generated_next seed response generated sample nonnegative)
  change NativeUnifiedHeatWrite.forcing seed (response.2.clockAdvance + sample) =
    NativeUnifiedHeatWrite.forcing response.1 sample at actual
  unfold kernel
  rw [actual, add_sub_add_left_eq_sub]

theorem window_generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    window seed (response.2.clockAdvance + a) (response.2.clockAdvance + b) = window response.1 a b := by
  have same := NativeFiniteMacroEvolution.source_generated_next_evolution response generated a a_nonnegative
  have state : NativeGlobalHilbertAction.sourceState seed (response.2.clockAdvance + a) =
      NativeGlobalHilbertAction.sourceState response.1 a := congrArg NativeNegativeFourMomentum.embed same
  have shift := intervalIntegral.integral_comp_add_left
    (kernel seed (response.2.clockAdvance + b)) response.2.clockAdvance (a := a) (b := b)
  have integral : (∫ sample in (response.2.clockAdvance + a)..(response.2.clockAdvance + b),
      kernel seed (response.2.clockAdvance + b) sample) = ∫ sample in a..b, kernel response.1 b sample := by
    refine shift.symm.trans ?_
    apply intervalIntegral.integral_congr
    intro sample inside
    rw [uIcc_of_le ordered] at inside
    exact kernel_generated_next seed response generated b sample (a_nonnegative.trans inside.1)
  have initial : translation ((response.2.clockAdvance + b) - (response.2.clockAdvance + a))
      (embed nu (NativeGlobalHilbertAction.sourceState seed (response.2.clockAdvance + a))) =
      translation (b - a) (embed nu (NativeGlobalHilbertAction.sourceState response.1 a)) :=
    congrArg₂ (fun time value => translation time (embed nu value)) (add_sub_add_left_eq_sub _ _ _) state
  exact congrArg₂ (fun left right : Ambient => left + right) initial integral

theorem generated_next_initial (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) :
    read nu (window seed 0 response.2.clockAdvance) = NativeGlobalHilbertAction.sourceState response.1 0 := by
  rw [window_read seed 0 response.2.clockAdvance le_rfl response.2.clockAdvance_pos.le]
  have same := NativeFiniteMacroEvolution.source_generated_next_evolution response generated 0 le_rfl
  change NativeNegativeFourMomentum.embed (NativeAbsoluteEventualControl.velocity seed response.2.clockAdvance) =
    NativeNegativeFourMomentum.embed (NativeAbsoluteEventualControl.velocity response.1 0)
  exact congrArg NativeNegativeFourMomentum.embed (by simpa only [add_zero] using same)

end
end SaturationMonoid.NavierStokes.NativeUnifiedDilationWrite
