import H0mework.NavierStokes.UnifiedAction.UnifiedStressSource
import H0mework.NavierStokes.UnifiedAction.UnifiedGlobalActionFeed

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedGlobalStressSource

open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeEndpointVelocityCarrier NativeStressSource NativeTimeJetCarrier
open NativeFiniteMacroPhysical NativeEventualTailControl NativeFiniteMacroEvolution

noncomputable section

variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

abbrev State := WholeRestartVelocityEndpointState × NativeFluidStressFourierState

def ordinary (velocity : WholeRestartVelocityEndpointState) : State :=
  (velocity, quadraticFlux (wholeVelocity velocity))

def initial (current : GeneratedWholeRestartCurrent nu) : State :=
  ordinary (puncturedWholeVelocityEuclideanState current.initialState)

def stage {next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) : State :=
  (step.physicalStageTrajectory time, NativeUnifiedStressSource.macroStress step time)

theorem stage_endpoint {next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    stage step step.clockAdvance = initial next := by
  apply Prod.ext
  · exact (step.physicalStageTrajectory_eq_stage step.physicalStageTerminal).trans step.physicalStage_terminal
  · exact NativeUnifiedStressSource.macroStress_terminal step

def history : {current : GeneratedWholeRestartCurrent nu} →
    NativeReachable seed generatedWholeRestartEndpointMacroRespond current → ℝ → State
  | _, .initial => fun _ => initial seed
  | _, .step (response := response) arrival _ => endpointSplice (clock arrival) (history arrival) (stage response.2)

theorem history_velocity (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) : (history arrival time).1 = path arrival time := by
  induction arrival with
  | initial => rfl
  | @step prior arrival response generated previous =>
      by_cases before : time ≤ clock arrival <;> simp [history, path, endpointSplice, before, previous, stage]

theorem history_endpoint (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    history arrival (clock arrival) = initial current := by
  cases arrival with
  | initial => rfl
  | @step prior arrival response generated =>
      have later : clock arrival < clock arrival + response.2.clockAdvance := by linarith [response.2.clockAdvance_pos]
      simp only [history, clock, endpointSplice_of_lt _ _ _ _ later, add_sub_cancel_left, stage_endpoint]

theorem history_zero (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    history arrival 0 = initial seed := by
  induction arrival with
  | initial => rfl
  | step arrival generated previous =>
      simpa only [history, endpointSplice_of_le _ _ _ _ (clock_nonnegative arrival)] using previous

theorem history_append_preserves {next : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : NativeReachable current generatedWholeRestartEndpointMacroRespond next)
    (time : ℝ) (before : time ≤ clock arrival) :
    history (BoundedRun.prependNativeReachable arrival suffix) time = history arrival time := by
  induction suffix with
  | initial => rfl
  | @step prior suffix response generated previous =>
      have bound : time ≤ clock (BoundedRun.prependNativeReachable arrival suffix) := by
        rw [clock_append]
        linarith [clock_nonnegative suffix]
      exact (endpointSplice_of_le _ _ _ _ bound).trans previous

theorem history_append_chart {next : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : NativeReachable current generatedWholeRestartEndpointMacroRespond next)
    (time : Icc (0 : ℝ) (clock suffix)) :
    history (BoundedRun.prependNativeReachable arrival suffix) (clock arrival + time.1) = history suffix time.1 := by
  induction suffix with
  | initial =>
      have zero : time.1 = 0 := le_antisymm time.2.2 time.2.1
      change history arrival (clock arrival + time.1) = initial current
      simpa only [zero, add_zero] using history_endpoint arrival
  | @step prior suffix response generated previous =>
      by_cases earlier : time.1 ≤ clock suffix
      · simp only [BoundedRun.prependNativeReachable, history]
        rw [endpointSplice_of_le _ _ _ _ (by rw [clock_append]; linarith),
          endpointSplice_of_le _ _ _ _ earlier]
        exact previous ⟨time.1, time.2.1, earlier⟩
      · have later : clock suffix < time.1 := lt_of_not_ge earlier
        change endpointSplice _ _ _ _ = endpointSplice _ _ _ _
        rw [clock_append, endpointSplice_of_lt _ _ _ _ (by linarith), endpointSplice_of_lt _ _ _ _ later]
        congr 1
        ring

def global (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) : ℝ → State :=
  endpointSplice (clock run.arrival) (history run.arrival)
    (fun time => ordinary (NativeFiniteMacroGlobal.tail run time))

theorem global_velocity (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (time : ℝ) :
    (global run time).1 = NativeFiniteMacroGlobal.globalPath run time := by
  by_cases before : time ≤ clock run.arrival <;>
    simp [global, NativeFiniteMacroGlobal.globalPath, endpointSplice, before, history_velocity, ordinary]

theorem global_after_arrival (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (suffix : GeneratedWholeRestartEndpointMacroTerminalRun current)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    global (prependTerminal arrival suffix) (clock arrival + time) = global suffix time := by
  by_cases earlier : time ≤ clock suffix.arrival
  · have total : clock (prependTerminal arrival suffix).arrival = clock arrival + clock suffix.arrival :=
      clock_append arrival suffix.arrival
    rw [global, global, endpointSplice_of_le _ _ _ _ (by rw [total]; linarith),
      endpointSplice_of_le _ _ _ _ earlier]
    exact history_append_chart arrival suffix.arrival ⟨time, nonnegative, earlier⟩
  · have later : clock suffix.arrival < time := lt_of_not_ge earlier
    unfold global
    rw [show clock (prependTerminal arrival suffix).arrival = clock arrival + clock suffix.arrival from
        clock_append arrival suffix.arrival,
      endpointSplice_of_lt _ _ _ _ (by linarith), endpointSplice_of_lt _ _ _ _ later]
    have offset : clock arrival + time - (clock arrival + clock suffix.arrival) = time - clock suffix.arrival := by ring
    rw [offset]
    rfl

def source (seed : GeneratedWholeRestartCurrent nu) : ℝ → State := global (terminal seed)

def stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : NativeFluidStressFourierState :=
  (source seed time).2

theorem source_zero (seed : GeneratedWholeRestartCurrent nu) : source seed 0 = initial seed := by
  rw [source, global, endpointSplice_of_le _ _ _ _ (clock_nonnegative (terminal seed).arrival)]
  exact history_zero (terminal seed).arrival

theorem source_velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (source seed time).1 = NativeAbsoluteEventualControl.velocity seed time := global_velocity _ _

theorem source_after_arrival (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    source seed (clock arrival + time) = source current time := by
  have same := terminal_unique (terminal seed) (prependTerminal arrival (terminal current))
  unfold source
  rw [same]
  exact global_after_arrival arrival (terminal current) time nonnegative

theorem source_generated_next (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    source seed (response.2.clockAdvance + time) = source response.1 time := by
  simpa only [clock, zero_add] using source_after_arrival (.step .initial generated) time nonnegative

theorem source_step_read (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (positive : 0 < time) (before : time ≤ response.2.clockAdvance) :
    source seed time = stage response.2 time := by
  let first : NativeReachable seed generatedWholeRestartEndpointMacroRespond response.1 := .step .initial generated
  have same := terminal_unique (terminal seed) (prependTerminal first (terminal response.1))
  have clockFirst : clock first = response.2.clockAdvance := by simp only [first, clock, zero_add]
  have clockWhole : clock (prependTerminal first (terminal response.1)).arrival =
      clock first + clock (terminal response.1).arrival := clock_append first (terminal response.1).arrival
  unfold source
  rw [same, global, endpointSplice_of_le _ _ _ _
    (by rw [clockWhole, clockFirst]; linarith [clock_nonnegative (terminal response.1).arrival])]
  change history (BoundedRun.prependNativeReachable first (terminal response.1).arrival) time = _
  rw [history_append_preserves first (terminal response.1).arrival time (by rwa [clockFirst])]
  change endpointSplice 0 _ _ time = _
  rw [endpointSplice_of_lt _ _ _ _ positive, sub_zero]

theorem source_cofinal_stress (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) :
    stress seed (wholeRestartVelocityAccumulationTime seed) =
      (NativeCofinalStress.sourceGeneratedCofinalStress seed).stress := by
  rw [stress, source_step_read response generated _ (NativeMacroMomentumIntegral.accumulation_positive response.2)
    (by rw [NativeMacroMomentumIntegral.clock_split]; linarith [(NativeMacroMomentumIntegral.recoveryTime_mem response.2).1])]
  exact NativeUnifiedStressSource.macroStress_cofinal response.2

theorem source_recovery_stress (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (NativeMacroMomentumIntegral.recoveryTime response.2)) :
    stress seed (wholeRestartVelocityAccumulationTime seed + time) = NativeUnifiedStressSource.rootStress seed time := by
  rw [stress, source_step_read response generated _
    (by linarith [NativeMacroMomentumIntegral.accumulation_positive response.2, inside.1])
    (by rw [NativeMacroMomentumIntegral.clock_split]; linarith [inside.2])]
  exact NativeUnifiedStressSource.macroStress_recovery response.2 time inside

theorem history_ae (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    history arrival =ᵐ[volume] fun time => ordinary (path arrival time) := by
  induction arrival with
  | initial => exact Eventually.of_forall fun _ => rfl
  | @step prior arrival response generated previous =>
      have stageSame : stage response.2 =ᵐ[volume] fun time => ordinary (response.2.physicalStageTrajectory time) :=
        (NativeUnifiedStressSource.macroStress_ae response.2).mono fun time same => by
          exact Prod.ext rfl same
      have joined := NativeUnifiedActionHistory.splice_ae (clock arrival) previous stageSame
      apply joined.mono
      intro time same
      change endpointSplice _ _ _ time = ordinary (endpointSplice _ _ _ time)
      rw [same]
      by_cases before : time ≤ clock arrival <;> simp [endpointSplice, before]

theorem stress_ae (seed : GeneratedWholeRestartCurrent nu) :
    stress seed =ᵐ[volume] fun time => quadraticFlux (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time)) := by
  filter_upwards [history_ae (terminal seed).arrival] with time same
  change (global (terminal seed) time).2 = quadraticFlux (wholeVelocity (NativeFiniteMacroGlobal.globalPath (terminal seed) time))
  by_cases before : time ≤ clock (terminal seed).arrival
  · simp only [global, NativeFiniteMacroGlobal.globalPath, endpointSplice_of_le _ _ _ _ before, same, ordinary]
  · simp only [global, NativeFiniteMacroGlobal.globalPath, endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before), ordinary]

def historyBudget : {current : GeneratedWholeRestartCurrent nu} →
    NativeReachable seed generatedWholeRestartEndpointMacroRespond current → ℝ
  | _, .initial => ‖puncturedWholeVelocityEuclideanState seed.initialState‖ ^ 2
  | _, .step (response := response) arrival _ => max (historyBudget arrival) (NativeUnifiedStressSource.macroBudget response.2)

theorem ordinary_bound (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector)
    (output input : Coordinate) : ‖(ordinary value).2 wave output input‖ ≤ ‖value‖ ^ 2 := by
  simpa only [ordinary, wholeVelocity_mass] using quadraticFlux_norm_le_mass (wholeVelocity value) wave output input

theorem history_bound (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖(history arrival time).2 wave output input‖ ≤ historyBudget arrival := by
  induction arrival with
  | initial => exact ordinary_bound _ _ _ _
  | @step prior arrival response generated previous =>
      by_cases before : time ≤ clock arrival
      · rw [history, endpointSplice_of_le _ _ _ _ before]
        exact previous.trans (le_max_left _ _)
      · rw [history, endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
        exact (NativeUnifiedStressSource.macroStress_bound response.2 (time - clock arrival) wave output input).trans (le_max_right _ _)

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  max (historyBudget (terminal seed).arrival) (‖puncturedWholeVelocityEuclideanState seed.initialState‖ ^ 2)

theorem stress_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) : ‖stress seed time wave output input‖ ≤ budget seed := by
  by_cases before : time ≤ clock (terminal seed).arrival
  · rw [stress, source, global, endpointSplice_of_le _ _ _ _ before]
    exact (history_bound _ time wave output input).trans (le_max_left _ _)
  · have later : clock (terminal seed).arrival < time := lt_of_not_ge before
    have same : NativeFiniteMacroGlobal.tail (terminal seed) (time - clock (terminal seed).arrival) =
        NativeAbsoluteEventualControl.velocity seed time := by
      rw [NativeAbsoluteEventualControl.velocity, NativeFiniteMacroGlobal.globalPath,
        endpointSplice_of_lt _ _ _ _ later]
    rw [stress, source, global, endpointSplice_of_lt _ _ _ _ later, same]
    exact ((ordinary_bound _ wave output input).trans
      (pow_le_pow_left₀ (norm_nonneg _) (NativeAbsoluteEventualControl.velocity_norm_le seed time) 2)).trans (le_max_right _ _)

def momentumRow (nu : Viscosity) (value : State) (wave : NonzeroIntegerWavevector) :=
  NativeNegativeFourMomentum.weightedRowCLM wave.1
    (projectedDivergenceCLM wave.1 (value.2 wave.1) -
      (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity value.1 wave.1)

theorem history_momentum (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) (wave : NonzeroIntegerWavevector) :
    NativeUnifiedActionHistory.historyAction (fun {_ _} => NativeUnifiedMacroActionFeed.action) arrival time wave =
      momentumRow nu (history arrival time) wave := by
  induction arrival with
  | initial => rfl
  | @step prior arrival response generated previous =>
      by_cases before : time ≤ clock arrival
      · simpa only [NativeUnifiedActionHistory.historyAction, history, endpointSplice_of_le _ _ _ _ before] using previous
      · simp only [NativeUnifiedActionHistory.historyAction, history, endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
        exact NativeUnifiedStressSource.macro_action_row response.2 _ wave

theorem global_momentum (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (time : ℝ)
    (wave : NonzeroIntegerWavevector) :
    NativeUnifiedActionHistory.global (fun {_ _} => NativeUnifiedMacroActionFeed.action) run time wave =
      momentumRow nu (global run time) wave := by
  by_cases before : time ≤ clock run.arrival
  · simpa only [NativeUnifiedActionHistory.global, global, endpointSplice_of_le _ _ _ _ before] using
      history_momentum run.arrival time wave
  · rw [NativeUnifiedActionHistory.global, global, endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before),
      endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
    rfl

theorem source_momentum (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : NonzeroIntegerWavevector) :
    NativeUnifiedGlobalActionFeed.action seed time wave = momentumRow nu (source seed time) wave :=
  global_momentum (terminal seed) time wave

end
end SaturationMonoid.NavierStokes.NativeUnifiedGlobalStressSource
