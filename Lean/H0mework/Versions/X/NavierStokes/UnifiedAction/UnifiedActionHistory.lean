import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedSourceDerivative

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedActionHistory

open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeFiniteMacroPhysical NativeEventualTailControl NativeFiniteMacroEvolution

noncomputable section

variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

abbrev StageAction (nu : Viscosity) :=
  {current next : GeneratedWholeRestartCurrent nu} →
    GeneratedWholeRestartEndpointMacroStep nu current next → ℝ → WholeRestartVelocityEndpointState

def initialAction (current : GeneratedWholeRestartCurrent nu) : WholeRestartVelocityEndpointState :=
  NativeNegativeFourMomentum.actionState nu (puncturedWholeVelocityEuclideanState current.initialState)

def historyAction (stage : StageAction nu) : {current : GeneratedWholeRestartCurrent nu} →
    NativeReachable seed generatedWholeRestartEndpointMacroRespond current → ℝ → WholeRestartVelocityEndpointState
  | _, .initial => fun _ => initialAction seed
  | _, .step (response := response) arrival _ => endpointSplice (clock arrival) (historyAction stage arrival) (stage response.2)

theorem splice_ae {E : Type*} (join : ℝ) {left right left' right' : ℝ → E}
    (before : left =ᵐ[volume] left') (after : right =ᵐ[volume] right') :
    endpointSplice join left right =ᵐ[volume] endpointSplice join left' right' := by
  have translated := (measurePreserving_sub_right (volume : Measure ℝ) join).quasiMeasurePreserving.ae after
  filter_upwards [before, translated] with time old new
  by_cases earlier : time ≤ join <;> simp [endpointSplice, earlier, old, new]

theorem prefix_ae (stage : StageAction nu)
    (stage_ae : ∀ {current next} (step : GeneratedWholeRestartEndpointMacroStep nu current next),
      stage step =ᵐ[volume] fun time => NativeNegativeFourMomentum.actionState nu (step.physicalStageTrajectory time))
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    historyAction stage arrival =ᵐ[volume] fun time => NativeNegativeFourMomentum.actionState nu (path arrival time) := by
  induction arrival with
  | initial => exact Eventually.of_forall fun _ => rfl
  | @step prior arrival response generated previous =>
      have same := splice_ae (clock arrival) previous (stage_ae response.2)
      apply same.mono
      intro time equality
      change endpointSplice (clock arrival) (historyAction stage arrival) (stage response.2) time =
        NativeNegativeFourMomentum.actionState nu (endpointSplice (clock arrival) (path arrival) response.2.physicalStageTrajectory time)
      rw [equality]
      by_cases before : time ≤ clock arrival <;> simp [endpointSplice, before]

theorem prefix_zero (stage : StageAction nu)
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    historyAction stage arrival 0 = initialAction seed := by
  induction arrival with
  | initial => rfl
  | step arrival generated previous =>
      simpa only [historyAction, endpointSplice_of_le _ _ _ _ (clock_nonnegative arrival)] using previous

theorem prefix_endpoint (stage : StageAction nu)
    (stage_endpoint : ∀ {current next} (step : GeneratedWholeRestartEndpointMacroStep nu current next),
      stage step step.clockAdvance = initialAction next)
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    historyAction stage arrival (clock arrival) = initialAction current := by
  cases arrival with
  | initial => rfl
  | @step prior arrival response generated =>
      have later : clock arrival < clock arrival + response.2.clockAdvance := by linarith [response.2.clockAdvance_pos]
      simp only [historyAction, clock, endpointSplice_of_lt _ _ _ _ later, add_sub_cancel_left, stage_endpoint]

theorem prefix_preserves (stage : StageAction nu)
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) current)
    (generated : generatedWholeRestartEndpointMacroRespond current = some response)
    (time : ℝ) (before : time ≤ clock arrival) :
    historyAction stage (.step arrival generated) time = historyAction stage arrival time :=
  endpointSplice_of_le _ _ _ _ before

theorem prefix_append_preserves (stage : StageAction nu)
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    {next : GeneratedWholeRestartCurrent nu}
    (suffix : NativeReachable current generatedWholeRestartEndpointMacroRespond next)
    (time : ℝ) (before : time ≤ clock arrival) :
    historyAction stage (BoundedRun.prependNativeReachable arrival suffix) time = historyAction stage arrival time := by
  induction suffix with
  | initial => rfl
  | @step prior suffix response generated previous =>
      have bound : time ≤ clock (BoundedRun.prependNativeReachable arrival suffix) := by
        rw [clock_append]
        linarith [clock_nonnegative suffix]
      exact (prefix_preserves stage _ response generated time bound).trans previous

theorem prefix_append_chart (stage : StageAction nu)
    (stage_endpoint : ∀ {current next} (step : GeneratedWholeRestartEndpointMacroStep nu current next),
      stage step step.clockAdvance = initialAction next)
    {next : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : NativeReachable current generatedWholeRestartEndpointMacroRespond next)
    (time : Icc (0 : ℝ) (clock suffix)) :
    historyAction stage (BoundedRun.prependNativeReachable arrival suffix) (clock arrival + time.1) = historyAction stage suffix time.1 := by
  induction suffix with
  | initial =>
      have zero : time.1 = 0 := le_antisymm time.2.2 time.2.1
      change historyAction stage arrival (clock arrival + time.1) = initialAction current
      simpa only [zero, add_zero] using prefix_endpoint stage stage_endpoint arrival
  | @step prior suffix response generated previous =>
      by_cases earlier : time.1 ≤ clock suffix
      · simp only [BoundedRun.prependNativeReachable]
        rw [prefix_preserves stage (BoundedRun.prependNativeReachable arrival suffix) response generated _
          (by rw [clock_append]; linarith), prefix_preserves stage suffix response generated _ earlier]
        exact previous ⟨time.1, time.2.1, earlier⟩
      · have later : clock suffix < time.1 := lt_of_not_ge earlier
        change endpointSplice _ _ _ _ = endpointSplice _ _ _ _
        rw [clock_append, endpointSplice_of_lt _ _ _ _ (by linarith), endpointSplice_of_lt _ _ _ _ later]
        congr 1
        ring

def global (stage : StageAction nu) (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) :
    ℝ → WholeRestartVelocityEndpointState :=
  endpointSplice (clock run.arrival) (historyAction stage run.arrival)
    (fun time => NativeNegativeFourMomentum.actionState nu (NativeFiniteMacroGlobal.tail run time))

theorem global_ae (stage : StageAction nu)
    (stage_ae : ∀ {current next} (step : GeneratedWholeRestartEndpointMacroStep nu current next),
      stage step =ᵐ[volume] fun time => NativeNegativeFourMomentum.actionState nu (step.physicalStageTrajectory time))
    (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) :
    global stage run =ᵐ[volume] fun time => NativeNegativeFourMomentum.actionState nu (NativeFiniteMacroGlobal.globalPath run time) := by
  filter_upwards [prefix_ae stage stage_ae run.arrival] with time same
  by_cases before : time ≤ clock run.arrival <;> simp [global, NativeFiniteMacroGlobal.globalPath, endpointSplice, before, same]

theorem global_after_arrival (stage : StageAction nu)
    (stage_endpoint : ∀ {current next} (step : GeneratedWholeRestartEndpointMacroStep nu current next),
      stage step step.clockAdvance = initialAction next)
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : GeneratedWholeRestartEndpointMacroTerminalRun current)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    global stage (prependTerminal arrival suffix) (clock arrival + time) = global stage suffix time := by
  by_cases earlier : time ≤ clock suffix.arrival
  · have total : clock (prependTerminal arrival suffix).arrival = clock arrival + clock suffix.arrival := clock_append arrival suffix.arrival
    rw [global, global, endpointSplice_of_le _ _ _ _ (by rw [total]; linarith), endpointSplice_of_le _ _ _ _ earlier]
    exact prefix_append_chart stage stage_endpoint arrival suffix.arrival ⟨time, nonnegative, earlier⟩
  · have later : clock suffix.arrival < time := lt_of_not_ge earlier
    unfold global
    rw [show clock (prependTerminal arrival suffix).arrival = clock arrival + clock suffix.arrival from clock_append arrival suffix.arrival,
      endpointSplice_of_lt _ _ _ _ (by linarith), endpointSplice_of_lt _ _ _ _ later]
    have offset : clock arrival + time - (clock arrival + clock suffix.arrival) = time - clock suffix.arrival := by ring
    rw [offset]
    rfl

end
end SaturationMonoid.NavierStokes.NativeUnifiedActionHistory
