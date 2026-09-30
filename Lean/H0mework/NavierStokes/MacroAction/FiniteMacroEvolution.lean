import H0mework.NavierStokes.SourceAction.AbsoluteEventual

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeFiniteMacroEvolution

open Set
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeFiniteMacroPhysical NativeEventualTailControl

noncomputable section

section Deterministic
universe u v
variable {State : Type u} {Step : State → State → Type v}
  {respond : ∀ state : State, Option (Response Step state)} {seed current : State}

theorem arrival_eq_of_length (first : NativeReachable seed respond current)
    {next : State} (second : NativeReachable seed respond next)
    (same : first.occurrence = second.occurrence) :
    (⟨current, first⟩ : Sigma (NativeReachable seed respond)) = ⟨next, second⟩ := by
  induction first generalizing next with
  | initial =>
      cases second with
      | initial => rfl
      | step prior generated => simp [NativeReachable.occurrence] at same
  | @step prior first response generated previous =>
      cases second with
      | initial => simp [NativeReachable.occurrence] at same
      | @step other second secondResponse secondGenerated =>
          have length : first.occurrence = second.occurrence := Nat.add_right_cancel same
          have equal := previous second length
          cases equal
          have responseEqual := Option.some.inj (generated.symm.trans secondGenerated)
          cases responseEqual
          rfl

theorem stopped_length_bound (first : NativeReachable seed respond current) (stopped : respond current = none)
    {next : State} (second : NativeReachable seed respond next) : second.occurrence ≤ first.occurrence := by
  induction second with
  | initial => exact Nat.zero_le _
  | @step prior second response generated previous =>
      have unequal : second.occurrence ≠ first.occurrence := by
        intro same
        have equal := arrival_eq_of_length second first same
        cases equal
        rw [stopped] at generated
        contradiction
      change second.occurrence + 1 ≤ first.occurrence
      omega

theorem stopped_arrival_eq (first : NativeReachable seed respond current) (firstStopped : respond current = none)
    {next : State} (second : NativeReachable seed respond next) (secondStopped : respond next = none) :
    (⟨current, first⟩ : Sigma (NativeReachable seed respond)) = ⟨next, second⟩ :=
  arrival_eq_of_length first second (Nat.le_antisymm
    (stopped_length_bound second secondStopped first) (stopped_length_bound first firstStopped second))

end Deterministic

variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

theorem terminal_unique (first second : GeneratedWholeRestartEndpointMacroTerminalRun seed) : first = second := by
  rcases first with ⟨first, firstArrival, firstStopped⟩
  rcases second with ⟨second, secondArrival, secondStopped⟩
  have equal := stopped_arrival_eq firstArrival firstStopped secondArrival secondStopped
  cases equal
  rfl

theorem path_append_chart {next : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : NativeReachable current generatedWholeRestartEndpointMacroRespond next)
    (time : Icc (0 : ℝ) (clock suffix)) :
    path (BoundedRun.prependNativeReachable arrival suffix) (clock arrival + time.1) = path suffix time.1 := by
  induction suffix with
  | initial =>
      have zero : time.1 = 0 := le_antisymm time.2.2 time.2.1
      change path arrival (clock arrival + time.1) = puncturedWholeVelocityEuclideanState current.initialState
      simpa only [zero, add_zero] using endpoint arrival
  | @step prior suffix response generated previous =>
      by_cases earlier : time.1 ≤ clock suffix
      · simp only [BoundedRun.prependNativeReachable]
        rw [step_preserves (BoundedRun.prependNativeReachable arrival suffix) response generated _ (by rw [clock_append]; linarith),
          step_preserves suffix response generated _ earlier]
        exact previous ⟨time.1, time.2.1, earlier⟩
      · have later : clock suffix < time.1 := lt_of_not_ge earlier
        change endpointSplice _ _ _ _ = endpointSplice _ _ _ _
        rw [clock_append,
          endpointSplice_of_lt _ _ _ _ (by linarith), endpointSplice_of_lt _ _ _ _ later]
        congr 1
        ring

def prependTerminal (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : GeneratedWholeRestartEndpointMacroTerminalRun current) : GeneratedWholeRestartEndpointMacroTerminalRun seed where
  terminal := suffix.terminal
  arrival := BoundedRun.prependNativeReachable arrival suffix.arrival
  stopped := suffix.stopped

theorem global_after_arrival (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : GeneratedWholeRestartEndpointMacroTerminalRun current)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    NativeFiniteMacroGlobal.globalPath (prependTerminal arrival suffix) (clock arrival + time) =
      NativeFiniteMacroGlobal.globalPath suffix time := by
  by_cases earlier : time ≤ clock suffix.arrival
  · rw [NativeFiniteMacroGlobal.prefix_preserved _ _ (by change _ ≤ clock (BoundedRun.prependNativeReachable arrival suffix.arrival); rw [clock_append]; linarith),
      NativeFiniteMacroGlobal.prefix_preserved _ _ earlier]
    exact path_append_chart arrival suffix.arrival ⟨time, nonnegative, earlier⟩
  · have later : clock suffix.arrival < time := lt_of_not_ge earlier
    unfold NativeFiniteMacroGlobal.globalPath
    change endpointSplice _ _ _ _ = endpointSplice _ _ _ _
    rw [show clock (prependTerminal arrival suffix).arrival = clock arrival + clock suffix.arrival from clock_append arrival suffix.arrival,
      endpointSplice_of_lt _ _ _ _ (by linarith), endpointSplice_of_lt _ _ _ _ later]
    have offset : clock arrival + time - (clock arrival + clock suffix.arrival) = time - clock suffix.arrival := by ring
    rw [offset]
    rfl

theorem source_after_arrival (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    NativeAbsoluteEventualControl.velocity seed (clock arrival + time) =
      NativeAbsoluteEventualControl.velocity current time := by
  have same := terminal_unique (terminal seed) (prependTerminal arrival (terminal current))
  unfold NativeAbsoluteEventualControl.velocity
  rw [same]
  exact global_after_arrival arrival (terminal current) time nonnegative

theorem source_generated_next_evolution
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    NativeAbsoluteEventualControl.velocity seed (response.2.clockAdvance + time) =
      NativeAbsoluteEventualControl.velocity response.1 time := by
  simpa only [clock, zero_add] using source_after_arrival (.step (.initial) generated) time nonnegative

end
end SaturationMonoid.NavierStokes.NativeFiniteMacroEvolution
