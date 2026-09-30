import H0mework.NavierStokes.WindowSourcePreparation.Action
import H0mework.NavierStokes.WindowPhysics.WindowJets

set_option autoImplicit false
open scoped Topology ENNReal Convolution ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowPreparationWrite
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeForwardWindowSource
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
noncomputable section
variable {nu : Viscosity}

def inactive : ℝ → ℝ := (Iic (0 : ℝ)).indicator (fun _ => 1)

theorem inactive_bound (time : ℝ) : ‖inactive time‖ ≤ 1 := by
  by_cases before : time ≤ 0 <;> simp [inactive, before]

theorem inactive_measurable : AEStronglyMeasurable inactive (volume : Measure ℝ) :=
  aestronglyMeasurable_const.indicator measurableSet_Iic

theorem inactive_locallyIntegrable : LocallyIntegrable inactive := by
  have bounded : MemLp inactive ∞ volume :=
    memLp_top_of_bound inactive_measurable 1 (Eventually.of_forall inactive_bound)
  exact bounded.locallyIntegrable le_top

def fraction : ℝ → ℝ := kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ] inactive

theorem fraction_smooth : ContDiff ℝ ∞ fraction :=
  kernel_compact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    kernel_smooth inactive_locallyIntegrable

theorem fraction_integrable (time : ℝ) : Integrable (fun shift : ℝ => kernel shift * inactive (time-shift)) :=
  kernel_compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    kernel_smooth.continuous inactive_locallyIntegrable time

theorem fraction_before (time : ℝ) (before : time ≤ -2) : fraction time = 1 := by
  change (∫ shift : ℝ, kernel shift * inactive (time-shift)) = 1
  rw [← kernel_mass]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernel shift = 0
  · simp only [zero, zero_mul]
  · have before : time-shift ≤ 0 := by linarith [(NativeViewPreparation.kernel_window shift zero).1]
    simp [inactive, before]

theorem fraction_after (time : ℝ) (after : -1 ≤ time) : fraction time = 0 := by
  change (∫ shift : ℝ, kernel shift * inactive (time-shift)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards with shift
  by_cases zero : kernel shift = 0
  · simp only [zero, zero_mul, Pi.zero_apply]
  · have after : ¬time-shift ≤ 0 := by linarith [kernel_support shift zero]
    simp [inactive, after]

def rate (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState :=
  momentumCLM nu (source seed time)-fraction time • momentumCLM nu (NativeUnifiedCompleteSource.source seed 0)

theorem rate_continuous (seed : GeneratedWholeRestartCurrent nu) : Continuous (rate seed) :=
  (NativeForwardWindowWrite.momentum_continuous seed).sub (fraction_smooth.continuous.smul continuous_const)

theorem rate_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    rate seed time = ∫ shift : ℝ, kernel shift • NativeWindowPreparationAction.action seed (time-shift) := by
  have original := (momentumCLM nu).integral_comp_comm (source_integrable seed time)
  have constant := (fraction_integrable time).smul_const (momentumCLM nu (NativeUnifiedCompleteSource.source seed 0))
  have integrable : Integrable (fun shift : ℝ => kernel shift •
      momentumCLM nu (NativeUnifiedCompleteSource.source seed (time-shift))) := by
    simpa only [Function.comp_def, map_smul] using
      (momentumCLM nu).integrable_comp (source_integrable seed time)
  simp only [map_smul] at original
  rw [rate, source_integrand, ← original]
  change (∫ shift : ℝ, kernel shift • momentumCLM nu (NativeUnifiedCompleteSource.source seed (time-shift)))-
    (∫ shift : ℝ, kernel shift * inactive (time-shift)) •
      momentumCLM nu (NativeUnifiedCompleteSource.source seed 0) = _
  rw [← integral_smul_const, ← integral_sub integrable constant]
  apply integral_congr_ae
  filter_upwards with shift
  rw [NativeWindowPreparationAction.action_correction, smul_sub]
  by_cases before : time-shift ≤ 0 <;> simp [inactive, before]

theorem action_product_integrable (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ) :
    Integrable (fun pair : ℝ × ℝ => kernel pair.2 • NativeWindowPreparationAction.action seed (pair.1-pair.2))
      ((volume.restrict (uIoc first last)).prod volume) := by
  let : IsFiniteMeasure (volume.restrict (uIoc first last)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min first last) (max first last)))
    infer_instance
  have measurable : AEStronglyMeasurable (fun pair : ℝ × ℝ =>
      kernel pair.2 • NativeWindowPreparationAction.action seed (pair.1-pair.2))
      ((volume : Measure ℝ).prod volume) :=
    kernel_smooth.continuous.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) (NativeWindowPreparationAction.action_measurable seed)
  apply ((kernel_integrable.mul_const (‖momentumCLM nu‖*NativeUnifiedCompleteSource.budget seed)).comp_snd
    (volume.restrict (uIoc first last))).mono'
    (measurable.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
  filter_upwards with pair
  rw [norm_smul, Real.norm_of_nonneg (kernel_nonnegative pair.2)]
  exact mul_le_mul_of_nonneg_left (NativeWindowPreparationAction.action_bound seed (pair.1-pair.2))
    (kernel_nonnegative pair.2)

theorem state_integral (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ) :
    NativeForwardWindowWrite.state seed last-NativeForwardWindowWrite.state seed first =
      ∫ time in first..last, rate seed time := by
  rw [NativeForwardWindowWrite.state, NativeForwardWindowWrite.state,
    ← integral_sub (NativeForwardWindowWrite.state_integrable seed last)
      (NativeForwardWindowWrite.state_integrable seed first)]
  simp_rw [rate_original]
  rw [intervalIntegral_integral_swap (action_product_integrable seed first last)]
  apply integral_congr_ae
  filter_upwards with shift
  rw [← smul_sub, NativeWindowPreparationAction.state_integral,
    ← intervalIntegral.integral_comp_sub_right, intervalIntegral.integral_smul]

theorem state_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    HasDerivAt (NativeForwardWindowWrite.state seed) (rate seed time) time := by
  have primitive := ((rate_continuous seed).integral_hasStrictDerivAt (-2) time).hasDerivAt
  have generated := primitive.const_add (NativeForwardWindowWrite.state seed (-2))
  apply generated.congr_of_eventuallyEq
  filter_upwards with nearby
  simpa only [add_comm] using eq_add_of_sub_eq (state_integral seed (-2) nearby)

theorem rate_after (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (after : -1 ≤ time) :
    rate seed time = momentumCLM nu (source seed time) := by
  rw [rate, fraction_after time after, zero_smul, sub_zero]

theorem full_integral (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ) :
    source seed last-source seed first = ∫ time in first..last, NativeForwardWindowJets.jet seed 1 time := by
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
    ((NativeForwardWindowJets.jet_smooth seed 1).continuous.intervalIntegrable first last)
  intro time _
  simpa only [NativeForwardWindowJets.jet_zero] using NativeForwardWindowJets.jet_hasDerivAt seed 0 time

theorem full_action_momentum (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    NativeForwardWindowWrite.stateCLM (NativeForwardWindowJets.jet seed 1 time) = rate seed time := by
  have actual := NativeForwardWindowWrite.stateCLM.hasFDerivAt.comp_hasDerivAt time
    (NativeForwardWindowJets.jet_hasDerivAt seed 0 time)
  have embedded : NativeForwardWindowWrite.stateCLM ∘ NativeForwardWindowJets.jet seed 0 =
      NativeForwardWindowWrite.state seed := by
    funext time
    rw [NativeForwardWindowJets.jet_zero, NativeForwardWindowWrite.state_embedded]
    rfl
  rw [embedded] at actual
  exact actual.unique (state_hasDerivAt seed time)

def generated (seed : GeneratedWholeRestartCurrent nu) (point : BasePoint) : FullSpace :=
  NativeUnifiedCompleteSource.source seed 0+
    (canonicalTimePrimitive (fun position => NativeForwardWindowJets.jet seed 1 (canonicalTimeProjection position)) point-
      canonicalTimePrimitive (fun position => NativeForwardWindowJets.jet seed 1 (canonicalTimeProjection position))
        (canonicalCauchySlicePoint (-2) (canonicalSpatialProjection point)))

theorem generated_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (space : StageNineSpatialPoint) :
    generated seed (canonicalCauchySlicePoint time space) = source seed time := by
  have actual := full_integral seed 0 time
  have initial := full_integral seed 0 (-2)
  rw [NativeWindowPreparationSource.window_initial seed (-2) le_rfl] at initial
  simp only [generated, canonicalTimePrimitive, canonicalTimeProjection_slice,
    canonicalSpatialProjection_slice]
  rw [← actual, ← initial]
  abel

theorem generated_initial (seed : GeneratedWholeRestartCurrent nu) (space : StageNineSpatialPoint) :
    generated seed (canonicalCauchySlicePoint (-2) space) = NativeUnifiedCompleteSource.source seed 0 := by
  rw [generated_original, NativeWindowPreparationSource.window_initial seed (-2) le_rfl]

theorem generated_full_action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (space : StageNineSpatialPoint) :
    HasDerivAt (fun clock => generated seed (canonicalCauchySlicePoint clock space))
      (NativeForwardWindowJets.jet seed 1 time) time := by
  simpa only [generated_original, NativeForwardWindowJets.jet_zero] using NativeForwardWindowJets.jet_hasDerivAt seed 0 time

theorem generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : SourceGeneratedNativeResponseDisposition.Response
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep nu) seed)
    (actual : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : StageNineSpatialPoint) :
    generated seed (canonicalCauchySlicePoint (response.2.clockAdvance+time) space) =
      generated response.1 (canonicalCauchySlicePoint time space) := by
  rw [generated_original, generated_original, source_next seed response actual time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowPreparationWrite
