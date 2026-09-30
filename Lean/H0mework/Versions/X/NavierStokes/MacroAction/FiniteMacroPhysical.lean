import H0mework.Realization.Process.NativeOccurrenceFold
import H0mework.Versions.X.NavierStokes.NormControl.Splice
import H0mework.NavierStokes.MacroRuntime.GlobalAbsoluteVelocity

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeFiniteMacroPhysical

open Set Filter
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeNormControl

noncomputable section

variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

def clock : {current : GeneratedWholeRestartCurrent nu} →
    NativeReachable seed generatedWholeRestartEndpointMacroRespond current → ℝ
  | _, .initial => 0
  | _, .step (response := response) arrival _ => clock arrival + response.2.clockAdvance

def path : {current : GeneratedWholeRestartCurrent nu} →
    NativeReachable seed generatedWholeRestartEndpointMacroRespond current → ℝ → WholeRestartVelocityEndpointState
  | _, .initial => fun _ => puncturedWholeVelocityEuclideanState seed.initialState
  | _, .step (response := response) arrival _ =>
      endpointSplice (clock arrival) (path arrival) response.2.physicalStageTrajectory

theorem clock_nonnegative (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) : 0 ≤ clock arrival := by
  induction arrival with
  | initial => rfl
  | @step prior arrival response generated previous => exact add_nonneg previous response.2.clockAdvance_pos.le

theorem endpoint (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    path arrival (clock arrival) = puncturedWholeVelocityEuclideanState current.initialState := by
  induction arrival with
  | initial => rfl
  | @step prior arrival response generated previous =>
      have later : clock arrival < clock arrival + response.2.clockAdvance := by linarith [response.2.clockAdvance_pos]
      simp only [path, clock, endpointSplice_of_lt _ _ _ _ later, add_sub_cancel_left]
      exact (response.2.physicalStageTrajectory_eq_stage response.2.physicalStageTerminal).trans response.2.physicalStage_terminal

theorem initial (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    path arrival 0 = puncturedWholeVelocityEuclideanState seed.initialState := by
  induction arrival with
  | initial => rfl
  | step arrival generated previous =>
      simpa only [path, endpointSplice_of_le _ _ _ _ (clock_nonnegative arrival)] using previous

theorem step_preserves (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) current)
    (generated : generatedWholeRestartEndpointMacroRespond current = some response) (time : ℝ) (before : time ≤ clock arrival) :
    path (.step arrival generated) time = path arrival time :=
  endpointSplice_of_le _ _ _ _ before

theorem step_chart (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) current)
    (generated : generatedWholeRestartEndpointMacroRespond current = some response)
    (time : Icc (0 : ℝ) response.2.clockAdvance) :
    path (.step arrival generated) (clock arrival + time.1) = response.2.physicalStage time := by
  by_cases atZero : time.1 = 0
  · simp only [atZero, add_zero, path, endpointSplice_of_le _ _ _ _ le_rfl, endpoint]
    have same : time = response.2.physicalStageZero := Subtype.ext atZero
    rw [same, response.2.physicalStage_zero]
  · have later : clock arrival < clock arrival + time.1 := by
      have positive : 0 < time.1 := lt_of_le_of_ne time.2.1 (Ne.symm atZero)
      linarith
    simp only [path, endpointSplice_of_lt _ _ _ _ later, add_sub_cancel_left]
    exact response.2.physicalStageTrajectory_eq_stage time

theorem clock_append {next : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : NativeReachable current generatedWholeRestartEndpointMacroRespond next) :
    clock (BoundedRun.prependNativeReachable arrival suffix) = clock arrival + clock suffix := by
  induction suffix with
  | initial => simp [BoundedRun.prependNativeReachable, clock]
  | step suffix generated previous => simp only [BoundedRun.prependNativeReachable, clock, previous, add_assoc]

theorem append_preserves {next : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : NativeReachable current generatedWholeRestartEndpointMacroRespond next)
    (time : ℝ) (before : time ≤ clock arrival) :
    path (BoundedRun.prependNativeReachable arrival suffix) time = path arrival time := by
  induction suffix with
  | initial => rfl
  | @step prior suffix response generated previous =>
      have bound : time ≤ clock (BoundedRun.prependNativeReachable arrival suffix) := by
        rw [clock_append]
        linarith [clock_nonnegative suffix]
      exact (step_preserves _ response generated time bound).trans previous

theorem actual_chart {next : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) current)
    (generated : generatedWholeRestartEndpointMacroRespond current = some response)
    (suffix : NativeReachable response.1 generatedWholeRestartEndpointMacroRespond next)
    (time : Icc (0 : ℝ) response.2.clockAdvance) :
    path (BoundedRun.prependNativeReachable (.step arrival generated) suffix) (clock arrival + time.1) =
      response.2.physicalStage time := by
  rw [append_preserves (.step arrival generated) suffix _ (by change _ ≤ clock arrival + response.2.clockAdvance; linarith [time.2.2])]
  exact step_chart arrival response generated time

theorem norm_le (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) (time : ℝ) :
    ‖path arrival time‖ ≤ ‖puncturedWholeVelocityEuclideanState seed.initialState‖ := by
  induction arrival generalizing time with
  | initial => rfl
  | @step prior arrival response generated previous =>
      by_cases before : time ≤ clock arrival
      · rw [path, endpointSplice_of_le _ _ _ _ before]
        exact previous time
      · rw [path, endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
        have source := macro_stage_velocity_norm_le response.2
          (projIcc (0 : ℝ) response.2.clockAdvance response.2.clockAdvance_pos.le (time - clock arrival))
        exact source.trans (by simpa only [endpoint] using previous (clock arrival))

theorem splice_continuous {E : Type*} [TopologicalSpace E] (joinTime : ℝ) (prior restart : ℝ → E)
    (priorContinuous : Continuous prior) (restartContinuous : Continuous restart) (same : restart 0 = prior joinTime) :
    Continuous (endpointSplice joinTime prior restart) := by
  unfold endpointSplice
  apply Continuous.if
  · intro time atBoundary
    change time ∈ frontier (Iic joinTime) at atBoundary
    rw [frontier_Iic] at atBoundary
    have atJoin : time = joinTime := by simpa using atBoundary
    subst time
    simp [same]
  · exact priorContinuous
  · exact restartContinuous.comp (continuous_id.sub continuous_const)

theorem coordinate_continuous (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (wave : NonzeroIntegerWavevector) : Continuous fun time => path arrival time wave := by
  induction arrival with
  | initial => exact continuous_const
  | @step prior arrival response generated previous =>
      have same : response.2.physicalStageTrajectory 0 wave = path arrival (clock arrival) wave := by
        have whole := (response.2.physicalStageTrajectory_eq_stage response.2.physicalStageZero).trans response.2.physicalStage_zero
        exact congrArg (fun value : WholeRestartVelocityEndpointState => value wave) (whole.trans (endpoint arrival).symm)
      have source := splice_continuous (clock arrival) (fun time => path arrival time wave)
        (fun time => response.2.physicalStageTrajectory time wave) previous
        (response.2.physicalStageTrajectory_coordinate_continuous wave) same
      convert source using 1
      funext time
      by_cases before : time ≤ clock arrival <;> simp [path, endpointSplice, before]

end
end SaturationMonoid.NavierStokes.NativeFiniteMacroPhysical
