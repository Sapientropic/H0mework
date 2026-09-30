import H0mework.NavierStokes.UnheatedWriterTail.Nonlinear
import H0mework.NavierStokes.StressWholeH1.Approximation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedSourceQuadraticApprox
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeFiniteActionResolvent NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Approximation
open NativeUnheatedSourceGradient NativeUnheatedSourceWeightedTail NativeEndpointVelocityCarrier
noncomputable section
variable {nu : Viscosity}

def physicalSource (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : wholePhysical :=
  if nonnegative : 0 ≤ time then physical seed time nonnegative else 0

theorem physicalSource_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (physicalSource seed) (volume : Measure ℝ) := by
  apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
  have original := (velocity_measurable seed).restrict.piecewise (s := Ici (0 : ℝ))
    (g := fun _ => (0 : State)) measurableSet_Ici aestronglyMeasurable_const
  apply original.congr
  filter_upwards with time
  by_cases nonnegative : 0 ≤ time <;> simp [physicalSource, physical, velocity, nonnegative]

def value (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State :=
  negativeAction (project radius (physicalSource seed time)) (project radius (physicalSource seed time))
    (H1_project radius _) (H1_project radius _)

theorem action_row_continuous (radius : ℕ) (wave : Wave) :
    Continuous (fun value : wholePhysical => negativeRow (project radius value) (project radius value) wave) := by
  have field := (physicalSpace (modes radius)).subtypeL.continuous.comp (restrict radius).continuous
  have mixed := (NativeCompleteStressBilinear.mixedCLM.continuous.comp field).clm_apply field
  have read := continuous_pi fun output => continuous_pi fun input =>
    (NativeCompleteStressCarrier.readCLM wave.1 output input).continuous.comp mixed
  have divergence := (NativeTimeJetCarrier.projectedDivergenceCLM wave.1).continuous.comp read
  have vector := NativeCompleteStressAction.euclideanCLM.continuous.comp divergence
  simpa only [Function.comp_def, Pi.smul_apply, negativeRow, NativeWholeH1Mixed.row, project_whole, NativeCompleteStressBilinear.mixedCLM_apply,
    NativeCompleteStressCarrier.readCLM_apply, NativeCompleteStressBilinear.mixed_read] using!
      vector.const_smul (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹

theorem value_measurable (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (value radius seed) (volume : Measure ℝ) := by
  have rows (wave : Wave) : AEStronglyMeasurable (fun time => value radius seed time wave) (volume : Measure ℝ) :=
    (action_row_continuous radius wave).comp_aestronglyMeasurable (physicalSource_measurable seed)
  let part (observed : Finset Wave) (time : ℝ) : State :=
    ∑ wave ∈ observed, lp.single 2 wave (value radius seed time wave)
  have measurable (observed : Finset Wave) : AEStronglyMeasurable (part observed) (volume : Measure ℝ) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable (rows wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Wave)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (value radius seed time)

theorem projected_action_bound (radius : ℕ) (value : wholePhysical) (regular : H1 value) :
    ‖negativeAction (project radius value) (project radius value) (H1_project radius value) (H1_project radius value)‖ ≤
      Real.sqrt NativeMovingCriticalProductWeights.constant * gradientMass value := by
  have below := project_mass_le radius value regular
  have mass0 : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative _)
  have paid := negativeAction_bound (project radius value) (project radius value) (H1_project radius value) (H1_project radius value)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) mass0)).mp
  rw [mul_pow, Real.sq_sqrt NativeMovingCriticalProductWeights.constant_nonnegative]
  apply paid.trans
  rw [pow_two, ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_left below NativeMovingCriticalProductWeights.constant_nonnegative) below
    (tsum_nonneg (gradient_nonnegative _)) (mul_nonneg NativeMovingCriticalProductWeights.constant_nonnegative mass0)

theorem value_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ radius,
      ‖value radius seed time‖ ≤ Real.sqrt NativeMovingCriticalProductWeights.constant * mass seed time := by
  filter_upwards [physical_H1_ae seed] with time regular nonnegative radius
  simpa only [value, physicalSource, dif_pos nonnegative, physical_mass] using
    projected_action_bound radius (physical seed time nonnegative) (regular nonnegative)

theorem value_tendsto_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → Tendsto (fun radius => value radius seed time) atTop (𝓝 (nonlinear seed time)) := by
  filter_upwards [physical_H1_ae seed] with time regular nonnegative
  simp only [value, physicalSource, nonlinear, dif_pos nonnegative, dif_pos (regular nonnegative)]
  exact negativeAction_project_tendsto _ _ (regular nonnegative) (regular nonnegative)

theorem value_integrable (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (value radius seed) (volume.restrict (Icc 0 horizon)) := by
  apply ((mass_integrable seed horizon nonnegative).const_mul (Real.sqrt NativeMovingCriticalProductWeights.constant)).mono'
    (value_measurable radius seed).restrict
  filter_upwards [ae_restrict_of_ae (value_bound_ae seed), ae_restrict_mem measurableSet_Icc] with time generated inside
  exact generated inside.1 radius

theorem quadratic_approximation (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon, ‖value radius seed time - nonlinear seed time‖) atTop (𝓝 0) := by
  have actual := tendsto_integral_of_dominated_convergence
    (fun time => 2 * Real.sqrt NativeMovingCriticalProductWeights.constant * mass seed time)
    (fun radius => ((value_measurable radius seed).sub (nonlinear_measurable seed)).norm.restrict)
    ((mass_integrable seed horizon nonnegative).const_mul (2 * Real.sqrt NativeMovingCriticalProductWeights.constant))
    (fun radius => by
      filter_upwards [ae_restrict_of_ae (value_bound_ae seed), ae_restrict_mem measurableSet_Icc] with time generated inside
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans ((add_le_add (generated inside.1 radius) (nonlinear_bound seed time)).trans_eq (by ring)))
    (by
      filter_upwards [ae_restrict_of_ae (value_tendsto_ae seed), ae_restrict_mem measurableSet_Icc] with time generated inside
      simpa only [Pi.sub_apply, sub_self, norm_zero] using! ((generated inside.1).sub_const (nonlinear seed time)).norm)
  simpa only [Pi.sub_apply, integral_zero] using! actual

theorem value_next (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    value radius seed (response.2.clockAdvance + time) = value radius response.1 time := by
  have later : 0 ≤ response.2.clockAdvance + time := add_nonneg response.2.clockAdvance_pos.le nonnegative
  have same : physicalSource seed (response.2.clockAdvance + time) = physicalSource response.1 time := by
    apply Subtype.ext
    simp only [physicalSource, dif_pos later, dif_pos nonnegative, physical,
      NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]
  simp only [value, same]

end
end SaturationMonoid.NavierStokes.NativeUnheatedSourceQuadraticApprox
