import H0mework.Versions.X.NavierStokes.UnheatedWriterTail.Nonlinear
import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.GlobalWindow
import H0mework.Versions.X.NavierStokes.StressEvolutionUnfiltered.Interpolation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedSourceWeightedTail

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open NativeResolventCompactness NativeWholeH1Mixed NativeWholeH1Pairing NativeGalerkinMovingProjection
open NativeUnheatedPairNegativeKernel NativeUnheatedPairGlobalEvolution NativeUnheatedSourceGradient

noncomputable section
variable {nu : Viscosity}

theorem nonlinear_sourceTriple (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    sourceTriple seed order time wave output input =
      bilinear nu order wave output input (nonlinear seed time) (NativeUnheatedGlobalNegativeOne.state seed time) +
      bilinear nu order wave output input (NativeUnheatedGlobalNegativeOne.state seed time) (nonlinear seed time) := by
  classical
  by_cases nonnegative : 0 ≤ time
  · by_cases regular : H1 (physical seed time nonnegative)
    · simp only [sourceTriple, nonlinear, dif_pos nonnegative, dif_pos regular]
    · simp only [sourceTriple, nonlinear, dif_pos nonnegative, dif_neg regular, map_zero, zero_apply, add_zero]
  · simp only [sourceTriple, nonlinear, dif_neg nonnegative, map_zero, zero_apply, add_zero]

def finiteTriple (seed : GeneratedWholeRestartCurrent nu) (order radius : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  let N := wholeRestartVelocityEndpointGalerkinInitialVelocity radius (nonlinear seed time)
  let U := wholeRestartVelocityEndpointGalerkinInitialVelocity radius (NativeUnheatedGlobalNegativeOne.state seed time)
  bilinear nu order wave output input N U + bilinear nu order wave output input U N

theorem state_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖NativeUnheatedGlobalNegativeOne.state seed time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
  (NativePhysicalTimeInterpolation.inverse_norm _).trans (velocity_bound seed time)

theorem finiteTriple_tendsto (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun radius => finiteTriple seed order radius time wave output input) atTop
      (𝓝 (sourceTriple seed order time wave output input)) := by
  rw [nonlinear_sourceTriple]
  let B := bilinear nu order wave output input
  have left := wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto (nonlinear seed time)
  have right := wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto (NativeUnheatedGlobalNegativeOne.state seed time)
  have continuous : Continuous (fun values : State × State => B values.1 values.2 + B values.2 values.1) :=
    ((B.continuous.comp continuous_fst).clm_apply continuous_snd).add
      ((B.continuous.comp continuous_snd).clm_apply continuous_fst)
  simpa only [finiteTriple, Function.comp_def, B] using!
    continuous.tendsto _ |>.comp (left.prodMk_nhds right)

theorem cubic_bound (B : State →L[ℝ] State →L[ℝ] ℂ) (N U : State) :
    ‖B N U + B U N‖ ≤ 2 * ‖B‖ * ‖N‖ * ‖U‖ :=
  (norm_add_le _ _).trans ((add_le_add (B.le_opNorm₂ N U) (B.le_opNorm₂ U N)).trans_eq (by ring))

theorem finiteTriple_error_bound (seed : GeneratedWholeRestartCurrent nu) (order radius : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖finiteTriple seed order radius time wave output input - sourceTriple seed order time wave output input‖ ≤
      (4 * ‖bilinear nu order wave output input‖ * NativeUnifiedCompleteSource.budget seed) * ‖nonlinear seed time‖ := by
  let B := bilinear nu order wave output input
  have first := cubic_bound B
    (wholeRestartVelocityEndpointGalerkinInitialVelocity radius (nonlinear seed time))
    (wholeRestartVelocityEndpointGalerkinInitialVelocity radius (NativeUnheatedGlobalNegativeOne.state seed time))
  have projected : ‖finiteTriple seed order radius time wave output input‖ ≤
      2 * ‖B‖ * ‖nonlinear seed time‖ * NativeUnifiedCompleteSource.budget seed := by
    apply first.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (projection_norm_le radius (nonlinear seed time)) (by positivity)
    · exact (projection_norm_le radius _).trans (state_bound seed time)
    · exact norm_nonneg _
    · positivity
  have original := cubic_bound B (nonlinear seed time) (NativeUnheatedGlobalNegativeOne.state seed time)
  rw [← nonlinear_sourceTriple] at original
  have bound := original.trans (mul_le_mul_of_nonneg_left (state_bound seed time) (by positivity))
  exact (norm_sub_le _ _).trans ((add_le_add projected bound).trans_eq (by ring))

theorem sourceTriple_tail_tendsto (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) (wave : IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon,
      ‖finiteTriple seed order radius time wave output input - sourceTriple seed order time wave output input‖)
      atTop (𝓝 0) := by
  have stateMeas := ((NativeUnheatedGlobalNegativeOne.state_continuousOn seed).mono
    (Icc_subset_Ici_self : Icc (0 : ℝ) horizon ⊆ Ici 0)).aestronglyMeasurable (μ := volume) measurableSet_Icc
  have nonlinearMeas := (nonlinear_measurable seed).restrict (s := Icc 0 horizon)
  let B := bilinear nu order wave output input
  have original := (B.aestronglyMeasurable_comp₂ nonlinearMeas stateMeas).add
    (B.aestronglyMeasurable_comp₂ stateMeas nonlinearMeas)
  have measured (radius : ℕ) : AEStronglyMeasurable (fun time =>
      ‖finiteTriple seed order radius time wave output input - sourceTriple seed order time wave output input‖)
      (volume.restrict (Icc 0 horizon)) := by
    have nl := (projection_continuous radius).comp_aestronglyMeasurable nonlinearMeas
    have st := (projection_continuous radius).comp_aestronglyMeasurable stateMeas
    have projected := (B.aestronglyMeasurable_comp₂ nl st).add (B.aestronglyMeasurable_comp₂ st nl)
    simpa only [finiteTriple, nonlinear_sourceTriple] using! (projected.sub original).norm
  have actual := tendsto_integral_of_dominated_convergence
    (fun time => (4 * ‖B‖ * NativeUnifiedCompleteSource.budget seed) * ‖nonlinear seed time‖)
    measured ((nonlinear_integrable seed horizon nonnegative).norm.const_mul _)
    (fun radius => Eventually.of_forall (fun time => by
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using finiteTriple_error_bound seed order radius time wave output input))
    (Eventually.of_forall (fun time => by
      simpa only [sub_self, norm_zero] using
        ((finiteTriple_tendsto seed order time wave output input).sub_const (sourceTriple seed order time wave output input)).norm))
  simpa only [integral_zero] using actual

theorem tripleWindow_as_tail (seed : GeneratedWholeRestartCurrent nu) (derivative order : ℕ)
    (time : ℝ) (valid : -1 ≤ time) :
    NativeUnheatedPairGlobalWindow.tripleWindow seed derivative order time =
      NativeUnheatedPairWindowTail.tail seed derivative order time +
        NativeUnheatedPairWindowTail.tail seed (derivative+1) (order+1) time :=
  sub_eq_iff_eq_add.mp (NativeUnheatedPairGlobalWindow.step seed derivative order time valid).symm

theorem tripleWindow_next (seed : GeneratedWholeRestartCurrent nu) (derivative order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    NativeUnheatedPairGlobalWindow.tripleWindow seed derivative order (response.2.clockAdvance + time) =
      NativeUnheatedPairGlobalWindow.tripleWindow response.1 derivative order time := by
  rw [tripleWindow_as_tail seed derivative order _ (by linarith [response.2.clockAdvance_pos]),
    tripleWindow_as_tail response.1 derivative order time (by linarith),
    NativeUnheatedPairWindowTail.tail_next seed derivative order response generated time nonnegative,
    NativeUnheatedPairWindowTail.tail_next seed (derivative+1) (order+1) response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedSourceWeightedTail
