import H0mework.NavierStokes.WindowPhysics.WindowSource

set_option autoImplicit false
open scoped Topology ENNReal Convolution ContDiff

namespace SaturationMonoid.NavierStokes.NativeForwardWindowWrite

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction
open NativeForwardWindowSource

noncomputable section

variable {nu : Viscosity}

def stateCLM : FullSpace →L[ℝ] WholeRestartVelocityEndpointState :=
  NativeNegativeFourMomentum.embed.comp
    (WithLp.fstL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space)

theorem stateCLM_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    stateCLM (NativeUnifiedCompleteSource.source seed time) =
      NativeGlobalHilbertAction.sourceState seed time := by
  change NativeNegativeFourMomentum.embed (NativeUnifiedCompleteSource.source seed time).fst = _
  rw [NativeUnifiedCompleteSource.velocity_read]
  rfl

def state (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState :=
  ∫ shift : ℝ, kernel shift • NativeGlobalHilbertAction.sourceState seed (time - shift)

theorem state_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Integrable (fun shift : ℝ => kernel shift • NativeGlobalHilbertAction.sourceState seed (time - shift)) := by
  simpa only [Function.comp_def, map_smul, stateCLM_original] using
    stateCLM.integrable_comp (source_integrable seed time)

theorem state_embedded (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    state seed time = NativeNegativeFourMomentum.embed (source seed time).fst := by
  have original := stateCLM.integral_comp_comm (source_integrable seed time)
  simpa only [map_smul, stateCLM_original, ← source_integrand] using! original

theorem momentum_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    momentumCLM nu (source seed time) =
      ∫ shift : ℝ, kernel shift • NativeUnifiedGlobalActionFeed.action seed (time - shift) := by
  have original := (momentumCLM nu).integral_comp_comm (source_integrable seed time)
  simpa only [map_smul, NativeUnifiedCompleteSource.source_momentum, ← source_integrand] using original.symm

theorem source_product_integrable (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) :
    Integrable (fun pair : ℝ × ℝ =>
      kernel pair.2 • NativeUnifiedCompleteSource.source seed (pair.1 - pair.2))
      ((volume.restrict (uIoc a b)).prod volume) := by
  let : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min a b) (max a b)))
    infer_instance
  have measurable : AEStronglyMeasurable (fun pair : ℝ × ℝ =>
      kernel pair.2 • NativeUnifiedCompleteSource.source seed (pair.1 - pair.2))
      ((volume : Measure ℝ).prod volume) :=
    kernel_smooth.continuous.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) (NativeUnifiedCompleteSource.source_measurable seed)
  apply ((kernel_integrable.mul_const (NativeUnifiedCompleteSource.budget seed)).comp_snd
    (volume.restrict (uIoc a b))).mono'
    (measurable.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
  filter_upwards with pair
  rw [norm_smul, Real.norm_of_nonneg (kernel_nonnegative pair.2)]
  exact mul_le_mul_of_nonneg_left
    (NativeUnifiedCompleteSource.source_bound seed (pair.1 - pair.2)) (kernel_nonnegative pair.2)

theorem action_product_integrable (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) :
    Integrable (fun pair : ℝ × ℝ =>
      kernel pair.2 • NativeUnifiedGlobalActionFeed.action seed (pair.1 - pair.2))
      ((volume.restrict (uIoc a b)).prod volume) := by
  simpa only [Function.comp_def, map_smul, NativeUnifiedCompleteSource.source_momentum] using
    (momentumCLM nu).integrable_comp (source_product_integrable seed a b)

theorem state_integral (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_valid : -1 ≤ a) (b_valid : -1 ≤ b) :
    state seed b - state seed a = ∫ time in a..b, momentumCLM nu (source seed time) := by
  rw [state, state, ← integral_sub (state_integrable seed b) (state_integrable seed a)]
  simp_rw [momentum_original]
  rw [intervalIntegral_integral_swap (action_product_integrable seed a b)]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernel shift = 0
  · simp only [zero, zero_smul, sub_self, intervalIntegral.integral_zero]
  · rw [← smul_sub, NativeUnifiedGlobalActionFeed.source_integral seed (a - shift) (b - shift)
      (by linarith [kernel_support shift zero]) (by linarith [kernel_support shift zero]),
      ← intervalIntegral.integral_comp_sub_right, intervalIntegral.integral_smul]

theorem momentum_continuous (seed : GeneratedWholeRestartCurrent nu) :
    Continuous (fun time => momentumCLM nu (source seed time)) :=
  (momentumCLM nu).continuous.comp (source_smooth seed).continuous

theorem state_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    HasDerivAt (state seed) (momentumCLM nu (source seed time)) time := by
  have primitive := ((momentum_continuous seed).integral_hasStrictDerivAt (-1) time).hasDerivAt
  have generated := primitive.const_add (state seed (-1))
  apply generated.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds valid] with nearby nearby_valid
  simpa only [add_comm] using eq_add_of_sub_eq (state_integral seed (-1) nearby le_rfl nearby_valid.le)

theorem state_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    state seed (response.2.clockAdvance + time) = state response.1 time := by
  rw [state_embedded, state_embedded, source_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeForwardWindowWrite
