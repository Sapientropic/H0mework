import H0mework.NavierStokes.StressAction.CompleteStressAction
import H0mework.NavierStokes.UnifiedAction.UnifiedGlobalStressSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedCompleteSource

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open SourceGeneratedNativeResponseDisposition
open NativeCompleteStressCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator

noncomputable section

variable {nu : Viscosity}

def stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Space :=
  ofBound (NativeUnifiedGlobalStressSource.stress seed time) (NativeUnifiedGlobalStressSource.budget seed)
    (NativeUnifiedGlobalStressSource.stress_bound seed time)

/-- One normed realization of the original history's complete velocity/stress pair. -/
def source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : FullSpace :=
  WithLp.toLp 2 ((NativeUnifiedGlobalStressSource.source seed time).1, stress seed time)

theorem velocity_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (source seed time).fst = NativeAbsoluteEventualControl.velocity seed time :=
  NativeUnifiedGlobalStressSource.source_velocity seed time

theorem stress_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    read (source seed time).snd = NativeUnifiedGlobalStressSource.stress seed time :=
  read_ofBound _ _ (NativeUnifiedGlobalStressSource.stress_bound seed time)

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  Real.sqrt (‖puncturedWholeVelocityEuclideanState seed.initialState‖ ^ 2 +
    9 * (NativeUnifiedGlobalStressSource.budget seed) ^ 2 * ∑' wave, weight wave ^ 2)

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖source seed time‖ ≤ budget seed := by
  apply Real.le_sqrt_of_sq_le
  rw [WithLp.prod_norm_sq_eq_of_L2, velocity_read]
  exact add_le_add
    (pow_le_pow_left₀ (norm_nonneg _) (NativeAbsoluteEventualControl.velocity_norm_le seed time) 2)
    (ofBound_norm_sq _ _ (NativeUnifiedGlobalStressSource.stress_bound seed time))

theorem source_momentum (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    momentumCLM nu (source seed time) = NativeUnifiedGlobalActionFeed.action seed time := by
  apply lp.ext
  funext wave
  exact (momentumCLM_source nu (NativeUnifiedGlobalStressSource.source seed time).1
    (NativeUnifiedGlobalStressSource.stress seed time) (NativeUnifiedGlobalStressSource.budget seed)
    (NativeUnifiedGlobalStressSource.stress_bound seed time) wave).trans
      (NativeUnifiedGlobalStressSource.source_momentum seed time wave).symm

theorem source_generated_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    source seed (response.2.clockAdvance + time) = source response.1 time := by
  have original := NativeUnifiedGlobalStressSource.source_generated_next response generated time nonnegative
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · exact congrArg (fun value : NativeUnifiedGlobalStressSource.State => value.1) original
  · apply read_injective
    exact (read_ofBound _ _ (NativeUnifiedGlobalStressSource.stress_bound seed _)).trans
      ((congrArg (fun value : NativeUnifiedGlobalStressSource.State => value.2) original).trans
        (read_ofBound _ _ (NativeUnifiedGlobalStressSource.stress_bound response.1 time)).symm)

theorem source_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time →
      HasDerivAt (NativeGlobalHilbertAction.sourceState seed) (momentumCLM nu (source seed time)) time := by
  simpa only [source_momentum] using NativeUnifiedGlobalActionFeed.source_hasDerivAt_ae seed

theorem source_integral (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    NativeGlobalHilbertAction.sourceState seed b - NativeGlobalHilbertAction.sourceState seed a =
      ∫ time in a..b, momentumCLM nu (source seed time) := by
  simp only [source_momentum]
  exact NativeUnifiedGlobalActionFeed.source_integral seed a b a_nonnegative b_nonnegative

theorem source_primitive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (space : StageNineSpatialPoint) :
    NativeGlobalHilbertAction.sourceState seed 0 +
      canonicalTimePrimitive (fun point => momentumCLM nu (source seed (canonicalTimeProjection point)))
        (canonicalCauchySlicePoint time space) = NativeGlobalHilbertAction.sourceState seed time := by
  simp only [source_momentum]
  exact NativeUnifiedGlobalActionFeed.generatedState_original seed time nonnegative space

private theorem lp_measurable {Index E : Type*} [Countable Index]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : ℝ → lp (fun _ : Index => E) 2)
    (rows : ∀ index, AEStronglyMeasurable (fun time => field time index) (volume : Measure ℝ)) :
    AEStronglyMeasurable field (volume : Measure ℝ) := by
  classical
  let partialSum (observed : Finset Index) (time : ℝ) : lp (fun _ : Index => E) 2 :=
    ∑ index ∈ observed, lp.single 2 index (field time index)
  have measurable (observed : Finset Index) : AEStronglyMeasurable (partialSum observed) volume := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro index _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : Index => E) 2 index).continuous
      |>.comp_aestronglyMeasurable (rows index)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Index)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (field time)

theorem velocity_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (NativeAbsoluteEventualControl.velocity seed) (volume : Measure ℝ) :=
  lp_measurable _ fun wave => (NativeFiniteMacroGlobal.coordinate_continuous
    (NativeEventualTailControl.terminal seed) wave).aestronglyMeasurable

private theorem quadratic_tensor_continuous (wave : IntegerWavevector) :
    Continuous (fun velocity : WholeRestartVelocityEndpointState =>
      tensor (NativeStressSource.quadraticFlux (wholeVelocity velocity) wave)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Coordinate × Coordinate => ℂ)).comp
  apply continuous_pi
  intro pair
  change Continuous fun velocity : WholeRestartVelocityEndpointState =>
    NativeHigherTimeJets.mixedFluxCLM wave pair.1 pair.2 (wholeVelocityCLM velocity) (wholeVelocityCLM velocity)
  exact (continuous_const.clm_apply wholeVelocityCLM.continuous).clm_apply wholeVelocityCLM.continuous

theorem stress_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (stress seed) (volume : Measure ℝ) := by
  apply lp_measurable
  intro wave
  have ordinary := ((quadratic_tensor_continuous wave).const_smul (weight wave)).comp_aestronglyMeasurable
    (velocity_measurable seed)
  apply ordinary.congr
  filter_upwards [NativeUnifiedGlobalStressSource.stress_ae seed] with time same
  change weight wave • tensor (NativeStressSource.quadraticFlux
    (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time)) wave) =
      weight wave • tensor (NativeUnifiedGlobalStressSource.stress seed time wave)
  rw [same]

theorem source_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (source seed) (volume : Measure ℝ) := by
  have actual := (WithLp.prod_continuous_toLp 2 WholeRestartVelocityEndpointState Space).comp_aestronglyMeasurable
    ((velocity_measurable seed).prodMk (stress_measurable seed))
  apply actual.congr
  filter_upwards with time
  exact congrArg (fun velocity => WithLp.toLp 2 (velocity, stress seed time))
    (NativeUnifiedGlobalStressSource.source_velocity seed time).symm

theorem source_Linfty (seed : GeneratedWholeRestartCurrent nu) :
    MemLp (source seed) ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound (source_measurable seed) (budget seed) (Eventually.of_forall (source_bound seed))

theorem source_Lp (seed : GeneratedWholeRestartCurrent nu) (exponent : ℝ≥0∞)
    {domain : Set ℝ} (compact : IsCompact domain) :
    MemLp (source seed) exponent (volume.restrict domain) ∧
      eLpNorm (source seed) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (budget seed) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have bounded : ∀ᵐ time ∂volume.restrict domain, ‖source seed time‖ ≤ budget seed :=
    Eventually.of_forall (source_bound seed)
  exact ⟨MemLp.of_bound (source_measurable seed).restrict (budget seed) bounded,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bounded⟩

end
end SaturationMonoid.NavierStokes.NativeUnifiedCompleteSource
