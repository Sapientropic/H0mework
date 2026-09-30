import H0mework.NavierStokes.UnheatedWriterTail.Quadratic
import H0mework.NavierStokes.UnheatedWriterTail.Cubic

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedSourceQuadraticCubic
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open NativeResolventCompactness NativeGalerkinMovingProjection NativeUnheatedSourceWeightedTail
open NativeUnheatedPairNegativeKernel NativeUnheatedPairGlobalEvolution NativeUnheatedSourceGradient
open NativeUnheatedSourceQuadraticApprox
noncomputable section
variable {nu : Viscosity}

def finite (seed : GeneratedWholeRestartCurrent nu) (order radius : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  let N := wholeRestartVelocityEndpointGalerkinInitialVelocity radius (value radius seed time)
  let U := wholeRestartVelocityEndpointGalerkinInitialVelocity radius (NativeUnheatedGlobalNegativeOne.state seed time)
  bilinear nu order wave output input N U + bilinear nu order wave output input U N

theorem finite_tendsto_ae (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ∀ᵐ time : ℝ, 0 ≤ time → Tendsto (fun radius => finite seed order radius time wave output input)
      atTop (𝓝 (sourceTriple seed order time wave output input)) := by
  filter_upwards [value_tendsto_ae seed] with time actual nonnegative
  rw [nonlinear_sourceTriple]
  let B := bilinear nu order wave output input
  have nonlinear := moving_input atTop id (fun radius => value radius seed time) (NativeUnheatedSourceWeightedTail.nonlinear seed time)
    tendsto_id (actual nonnegative)
  have velocity := wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto (NativeUnheatedGlobalNegativeOne.state seed time)
  have continuous : Continuous (fun values : State × State => B values.1 values.2 + B values.2 values.1) :=
    ((B.continuous.comp continuous_fst).clm_apply continuous_snd).add
      ((B.continuous.comp continuous_snd).clm_apply continuous_fst)
  simpa only [finite, Function.comp_def, B, id_eq] using! continuous.tendsto _ |>.comp (nonlinear.prodMk_nhds velocity)

theorem finite_error_bound_ae (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ radius,
      ‖finite seed order radius time wave output input - sourceTriple seed order time wave output input‖ ≤
        (4 * ‖bilinear nu order wave output input‖ * NativeUnifiedCompleteSource.budget seed *
          Real.sqrt NativeMovingCriticalProductWeights.constant) * mass seed time := by
  filter_upwards [value_bound_ae seed] with time actual nonnegative radius
  let B := bilinear nu order wave output input
  have finiteBound : ‖finite seed order radius time wave output input‖ ≤
      2 * ‖B‖ * (Real.sqrt NativeMovingCriticalProductWeights.constant * mass seed time) * NativeUnifiedCompleteSource.budget seed := by
    apply (cubic_bound B _ _).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left ((projection_norm_le radius _).trans (actual nonnegative radius)) (by positivity)
    · exact (projection_norm_le radius _).trans (state_bound seed time)
    · exact norm_nonneg _
    · positivity [mass_nonnegative seed time]
  have original := cubic_bound B (nonlinear seed time) (NativeUnheatedGlobalNegativeOne.state seed time)
  rw [← nonlinear_sourceTriple] at original
  have originalBound := original.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (nonlinear_bound seed time) (by positivity))
    (state_bound seed time) (norm_nonneg _) (by positivity [mass_nonnegative seed time]))
  exact (norm_sub_le _ _).trans ((add_le_add finiteBound originalBound).trans_eq (by ring))

theorem actual_cubic_approximation (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon,
      ‖finite seed order radius time wave output input - sourceTriple seed order time wave output input‖)
      atTop (𝓝 0) := by
  have stateMeas := ((NativeUnheatedGlobalNegativeOne.state_continuousOn seed).mono
    (Icc_subset_Ici_self : Icc (0 : ℝ) horizon ⊆ Ici 0)).aestronglyMeasurable (μ := volume) measurableSet_Icc
  let B := bilinear nu order wave output input
  have original := (B.aestronglyMeasurable_comp₂ (nonlinear_measurable seed).restrict stateMeas).add
    (B.aestronglyMeasurable_comp₂ stateMeas (nonlinear_measurable seed).restrict)
  have measured (radius : ℕ) : AEStronglyMeasurable (fun time =>
      ‖finite seed order radius time wave output input - sourceTriple seed order time wave output input‖)
      (volume.restrict (Icc 0 horizon)) := by
    have nl := (projection_continuous radius).comp_aestronglyMeasurable ((value_measurable radius seed).restrict (s := Icc 0 horizon))
    have st := (projection_continuous radius).comp_aestronglyMeasurable stateMeas
    have projected := (B.aestronglyMeasurable_comp₂ nl st).add (B.aestronglyMeasurable_comp₂ st nl)
    simpa only [finite, nonlinear_sourceTriple] using! (projected.sub original).norm
  have actual := tendsto_integral_of_dominated_convergence
    (fun time => (4 * ‖B‖ * NativeUnifiedCompleteSource.budget seed * Real.sqrt NativeMovingCriticalProductWeights.constant) * mass seed time)
    measured ((mass_integrable seed horizon nonnegative).const_mul _)
    (fun radius => by
      filter_upwards [ae_restrict_of_ae (finite_error_bound_ae seed order wave output input), ae_restrict_mem measurableSet_Icc]
        with time generated inside
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using generated inside.1 radius)
    (by
      filter_upwards [ae_restrict_of_ae (finite_tendsto_ae seed order wave output input), ae_restrict_mem measurableSet_Icc]
        with time generated inside
      simpa only [sub_self, norm_zero] using
        ((generated inside.1).sub_const (sourceTriple seed order time wave output input)).norm)
  simpa only [integral_zero] using actual

theorem finite_next (seed : GeneratedWholeRestartCurrent nu) (order radius : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    finite seed order radius (response.2.clockAdvance + time) = finite response.1 order radius time := by
  funext wave output input
  simp only [finite, value_next radius seed response generated time nonnegative,
    NativeUnheatedGlobalNegativeOne.state_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedSourceQuadraticCubic
