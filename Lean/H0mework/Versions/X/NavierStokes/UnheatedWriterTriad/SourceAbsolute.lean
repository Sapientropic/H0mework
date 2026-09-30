import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Source
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Absolute

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedSourceGradient NativeUnheatedTriadChannels
noncomputable section
variable {nu : Viscosity}

def row (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) : ℂ :=
  NativeUnheatedTriadSum.term (kernel nu slot i j output) wave i j spectator
    (input seed slot 0 time) (input seed slot 1 time) (input seed slot 2 time) indices

theorem row_measurable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector) :
    AEStronglyMeasurable (row seed slot wave i j output spectator indices) (volume : Measure ℝ) := by
  have read (index : Fin 3) (k : IntegerWavevector) (coordinate : Coordinate) :
      AEStronglyMeasurable (fun time => input seed slot index time k coordinate) (volume : Measure ℝ) := by
    let evaluation := (ContinuousLinearMap.proj coordinate : (Coordinate → ℂ) →L[ℝ] ℂ).comp
      (lp.evalCLM ℝ (fun _ : IntegerWavevector => Coordinate → ℂ) 2 k)
    exact evaluation.continuous.comp_aestronglyMeasurable (input_measurable seed slot index)
  exact (((read 0 indices.2 i).mul (read 1 (wave-indices.1-indices.2) j)).const_mul
    (kernel nu slot i j output indices.2 (wave-indices.1-indices.2) indices.1)).mul (read 2 indices.1 spectator)

theorem row_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    Summable (fun indices => ‖row seed slot wave i j output spectator indices time‖) :=
  NativeUnheatedTriadSum.absolute_summable (kernel nu slot i j output) (cap nu)
    (kernel_bound nu slot i j output) wave i j spectator
    (input seed slot 0 time) (input seed slot 1 time) (input seed slot 2 time)

theorem row_sum_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) :
    (∑' indices, ‖row seed slot wave i j output spectator indices time‖) ≤ bound seed * mass seed time := by
  have generated := NativeUnheatedTriadSum.absolute_bound (kernel nu slot i j output) (cap nu)
    (kernel_bound nu slot i j output) wave i j spectator
    (input seed slot 0 time) (input seed slot 1 time) (input seed slot 2 time)
  have scalar0 : 0 ≤ 3 * cap nu * ‖NativeUnheatedTriadSum.weights‖ := by unfold cap; positivity [nu.coeff_pos]
  have paid := mul_le_mul_of_nonneg_left (input_product seed slot time) scalar0
  exact generated.trans (by simpa only [bound, mul_assoc, mul_left_comm, mul_comm] using paid)

theorem row_integrable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : IntegerWavevector × IntegerWavevector)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (row seed slot wave i j output spectator indices) (volume.restrict (Icc 0 horizon)) := by
  apply ((mass_integrable seed horizon nonnegative).const_mul (bound seed)).mono'
    (row_measurable seed slot wave i j output spectator indices).restrict
  apply Eventually.of_forall
  intro time
  exact ((row_summable seed slot wave i j output spectator time).le_tsum indices (fun _ _ => norm_nonneg _)).trans
    (row_sum_bound seed slot wave i j output spectator time)

theorem row_finite_integral_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (indices : Finset (IntegerWavevector × IntegerWavevector))
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∑ index ∈ indices, ∫ time in Icc 0 horizon, ‖row seed slot wave i j output spectator index time‖) ≤
      bound seed * NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon := by
  rw [← integral_finsetSum _ (fun index _ => (row_integrable seed slot wave i j output spectator index horizon nonnegative).norm)]
  calc
    _ ≤ ∫ time in Icc 0 horizon, bound seed * mass seed time := by
      apply integral_mono (integrable_finsetSum _ (fun index _ =>
        (row_integrable seed slot wave i j output spectator index horizon nonnegative).norm))
        ((mass_integrable seed horizon nonnegative).const_mul (bound seed))
      intro time
      exact ((row_summable seed slot wave i j output spectator time).sum_le_tsum indices
        (fun _ _ => norm_nonneg _)).trans (row_sum_bound seed slot wave i j output spectator time)
    _ = bound seed * ∫ time in Icc 0 horizon, mass seed time := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (mass_integral_bound seed horizon nonnegative) (bound_nonnegative seed)

theorem row_integrals_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Summable (fun indices => ∫ time in Icc 0 horizon, ‖row seed slot wave i j output spectator indices time‖) :=
  summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (row_finite_integral_bound seed slot wave i j output spectator · horizon nonnegative)

theorem integral_eq_row_sum (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, coefficient seed slot wave i j output spectator time) =
      ∑' indices, ∫ time in Icc 0 horizon, row seed slot wave i j output spectator indices time := by
  rw [integral_tsum_of_summable_integral_norm
    (fun index => row_integrable seed slot wave i j output spectator index horizon nonnegative)
    (row_integrals_summable seed slot wave i j output spectator horizon nonnegative)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro time
  exact NativeUnheatedTriadSum.value_eq_tsum (kernel nu slot i j output) (cap nu)
    (kernel_bound nu slot i j output) wave i j spectator
    (input seed slot 0 time) (input seed slot 1 time) (input seed slot 2 time)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadSource
