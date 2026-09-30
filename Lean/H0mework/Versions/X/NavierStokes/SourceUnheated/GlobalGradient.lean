import H0mework.Versions.X.NavierStokes.SourceUnheated.MacroGradient
import H0mework.Versions.X.NavierStokes.SourceAction.AbsoluteEventual

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedGlobalGradient
open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeFiniteMacroPhysical NativeFiniteMacroGlobal NativeUnheatedBandGradient
noncomputable section
variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

def pathBudget : {current : GeneratedWholeRestartCurrent nu} →
    NativeReachable seed generatedWholeRestartEndpointMacroRespond current → ℝ
  | _, .initial => 0
  | _, .step (response := response) arrival _ => pathBudget arrival + NativeUnheatedMacroGradient.budget response.2

theorem path_band_continuous (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (waves : Finset NonzeroIntegerWavevector) : Continuous (fun time => band waves (path arrival time)) :=
  band_curve_continuous (NativeFiniteMacroPhysical.coordinate_continuous arrival) waves

theorem path_integral_bound (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in 0..clock arrival, band waves (path arrival time)) ≤ pathBudget arrival := by
  induction arrival with
  | initial => simp only [clock, pathBudget, intervalIntegral.integral_same, le_refl]
  | @step prior arrival response generated previous =>
    have continuous := path_band_continuous (.step arrival generated) waves
    have before : (∫ time in 0..clock arrival, band waves (path (.step arrival generated) time)) =
        ∫ time in 0..clock arrival, band waves (path arrival time) := by
      apply intervalIntegral.integral_congr
      intro time inside
      rw [uIcc_of_le (clock_nonnegative arrival)] at inside
      change band waves (path (.step arrival generated) time) = _
      rw [step_preserves arrival response generated time inside.2]
    have after : (∫ time in clock arrival..clock arrival + response.2.clockAdvance,
        band waves (path (.step arrival generated) time)) =
        ∫ time in 0..response.2.clockAdvance, band waves (response.2.physicalStageTrajectory time) := by
      have shifted := intervalIntegral.integral_comp_add_left
        (f := fun time => band waves (path (.step arrival generated) time))
        (a := 0) (b := response.2.clockAdvance) (clock arrival)
      simp only [add_zero] at shifted
      rw [← shifted]
      apply intervalIntegral.integral_congr
      intro time inside
      rw [uIcc_of_le response.2.clockAdvance_pos.le] at inside
      change band waves (path (.step arrival generated) (clock arrival + time)) = band waves (response.2.physicalStageTrajectory time)
      rw [step_chart arrival response generated ⟨time, inside⟩, response.2.physicalStageTrajectory_eq_stage ⟨time, inside⟩]
    change (∫ time in 0..clock arrival + response.2.clockAdvance, band waves (path (.step arrival generated) time)) ≤ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable 0 (clock arrival))
      (continuous.intervalIntegrable (clock arrival) (clock arrival + response.2.clockAdvance)), before, after]
    exact add_le_add previous (NativeUnheatedMacroGradient.stage_integral_bound response.2 waves)


def tailReceipt (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (horizon : ℝ) :=
  (WholeGlobalReceipt.ofTrajectory run.globalPhysicalTrajectory).receiptAt (max horizon 0 + 1)
    (by linarith [le_max_right horizon 0])

def tailCeiling (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (horizon : ℝ) : ℝ :=
  biotSavartSerrinConstant * (3 * ‖(tailReceipt run horizon).wholePath‖ ^ 2)

theorem tail_band_bound (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (horizon : ℝ)
    (waves : Finset NonzeroIntegerWavevector) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
    band waves (tail run time) ≤ tailCeiling run horizon := by
  let point : Icc (0 : ℝ) (max horizon 0 + 1) := ⟨time, inside.1, by linarith [le_max_left horizon 0, inside.2]⟩
  have read := WholeGlobalReceipt.ofTrajectory_path run.globalPhysicalTrajectory (max horizon 0 + 1)
    (by linarith [le_max_right horizon 0]) point
  change (tailReceipt run horizon).wholePath point = run.globalPhysicalTrajectory.physicalPath time at read
  rw [tail, max_eq_left inside.1, ← read]
  apply (band_biot_bound waves _).trans
  apply mul_le_mul_of_nonneg_left _ biotSavartSerrinConstant_nonneg
  apply (wholeVorticityEuclideanMass_le_three_mul_norm_sq _).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) ((tailReceipt run horizon).wholePath.norm_coe_le_norm point) 2) (by norm_num)

theorem tail_integral_bound (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in 0..horizon, band waves (tail run time)) ≤ horizon * tailCeiling run horizon := by
  have actual := intervalIntegral.integral_mono_on (μ := volume) nonnegative
    (((band_continuous waves).comp (tail_continuous run)).intervalIntegrable 0 horizon)
    (intervalIntegrable_const (c := tailCeiling run horizon)) (fun time inside => tail_band_bound run horizon waves time inside)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, Function.comp_def] using! actual

def budget (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (horizon : ℝ) : ℝ :=
  pathBudget run.arrival + max horizon 0 * tailCeiling run horizon

theorem global_integral_bound (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in 0..horizon, band waves (globalPath run time)) ≤ budget run horizon := by
  have continuous := band_curve_continuous (NativeFiniteMacroGlobal.coordinate_continuous run) waves
  have before : (∫ time in 0..clock run.arrival, band waves (globalPath run time)) =
      ∫ time in 0..clock run.arrival, band waves (path run.arrival time) := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le (clock_nonnegative run.arrival)] at inside
    change band waves (globalPath run time) = _
    rw [prefix_preserved run time inside.2]
  have after : (∫ time in clock run.arrival..clock run.arrival + horizon, band waves (globalPath run time)) =
      ∫ time in 0..horizon, band waves (tail run time) := by
    have shifted := intervalIntegral.integral_comp_add_left (f := fun time => band waves (globalPath run time))
      (a := 0) (b := horizon) (clock run.arrival)
    simp only [add_zero] at shifted
    rw [← shifted]
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le nonnegative] at inside
    change band waves (globalPath run (clock run.arrival + time)) = band waves (tail run time)
    rw [tail_chart run time inside.1, tail, max_eq_left inside.1]
  have extended : (∫ time in 0..clock run.arrival + horizon, band waves (globalPath run time)) ≤ budget run horizon := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable 0 (clock run.arrival))
      (continuous.intervalIntegrable (clock run.arrival) (clock run.arrival + horizon)), before, after]
    rw [budget, max_eq_left nonnegative]
    exact add_le_add (path_integral_bound run.arrival waves) (tail_integral_bound run horizon nonnegative waves)
  have restricted : (∫ time in 0..horizon, band waves (globalPath run time)) ≤
      ∫ time in 0..clock run.arrival + horizon, band waves (globalPath run time) :=
    intervalIntegral.integral_mono_interval le_rfl nonnegative (by linarith [clock_nonnegative run.arrival])
      (Eventually.of_forall fun time => band_nonnegative waves (globalPath run time))
      (continuous.intervalIntegrable 0 (clock run.arrival + horizon))
  exact restricted.trans extended


theorem budget_nonnegative (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) : 0 ≤ budget run horizon := by
  simpa only [band, Finset.sum_empty, intervalIntegral.integral_zero] using
    global_integral_bound run horizon nonnegative ∅

theorem source_interval_bound (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in a..b, band waves (NativeAbsoluteEventualControl.velocity seed time)) ≤
      budget (NativeEventualTailControl.terminal seed) b := by
  have continuous := band_curve_continuous (NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed)) waves
  have restricted : (∫ time in a..b, band waves (NativeAbsoluteEventualControl.velocity seed time)) ≤
      ∫ time in 0..b, band waves (NativeAbsoluteEventualControl.velocity seed time) :=
    intervalIntegral.integral_mono_interval a_nonnegative ordered le_rfl
      (Eventually.of_forall fun time => band_nonnegative waves (NativeAbsoluteEventualControl.velocity seed time))
      (continuous.intervalIntegrable 0 b)
  exact restricted.trans (global_integral_bound (NativeEventualTailControl.terminal seed) b (a_nonnegative.trans ordered) waves)

end
end SaturationMonoid.NavierStokes.NativeUnheatedGlobalGradient
