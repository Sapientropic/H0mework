import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedMacroActionFeed

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedStressSource

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeRecoveryUnifiedCurrent NativeRecoveryAEWindows NativeEndpointVelocityCarrier
open NativeStressSource NativeStressCurlAlgebra NativeTimeJetCarrier NativeCofinalStress
open NativeMacroMomentumIntegral

noncomputable section

variable {nu : Viscosity}

def rootOrdinary (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) : NativeFluidStressFourierState :=
  quadraticFlux (velocity initial time)

def rootStress (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) : NativeFluidStressFourierState := by
  classical
  exact if time = 0 then (sourceGeneratedCofinalStress initial).stress else
    if inside : time ∈ Ioo (0 : ℝ) (terminal initial) then NativeRecoveryJointCurrent.stress initial ⟨time, inside⟩
      else rootOrdinary initial time

def rootBudget (initial : GeneratedWholeRestartCurrent nu) : ℝ :=
  max (NativeRecoveryJointCurrent.budget initial) (‖wholeRestartContactVelocityState initial 0‖ ^ 2)

theorem rootOrdinary_bound (initial : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖rootOrdinary initial time wave output input‖ ≤ NativeRecoveryJointCurrent.budget initial := by
  have physical := recoveryCurve_full (receipt initial) time
  change wholeVelocity (recoveryCurve (receipt initial) time) = velocity initial time at physical
  rw [rootOrdinary, ← physical]
  have raw := quadraticFlux_norm_le_mass (wholeVelocity (recoveryCurve (receipt initial) time)) wave output input
  rw [wholeVelocity_mass] at raw
  exact raw.trans (pow_le_pow_left₀ (norm_nonneg _)
    (NativeRecoveryEscapeCarrier.endpoint_norm_bound
      (receipt := receipt initial) (projIcc (0 : ℝ) 1 zero_le_one time)) 2)

theorem rootStress_bound (initial : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖rootStress initial time wave output input‖ ≤ rootBudget initial := by
  classical
  unfold rootStress
  split_ifs with zero inside
  · exact ((sourceGeneratedCofinalStress initial).stress_norm_le wave output input).trans (le_max_right _ _)
  · exact (NativeRecoveryJointCurrent.stress_bound initial ⟨time, inside⟩ wave output input).trans (le_max_left _ _)
  · exact (rootOrdinary_bound initial time wave output input).trans (le_max_left _ _)

theorem rootStress_zero (initial : GeneratedWholeRestartCurrent nu) :
    rootStress initial 0 = (sourceGeneratedCofinalStress initial).stress := by simp [rootStress]

theorem rootStress_at_time (initial : GeneratedWholeRestartCurrent nu) (time : NativeRecoveryJointCurrent.Time initial) :
    rootStress initial time.1 = NativeRecoveryJointCurrent.stress initial time := by
  simp only [rootStress, if_neg time.2.1.ne', dif_pos time.2]

theorem rootStress_terminal (initial : GeneratedWholeRestartCurrent nu) :
    rootStress initial (terminal initial) = rootOrdinary initial (terminal initial) := by
  have positive : 0 < terminal initial := (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time_pos
  rw [rootStress, if_neg positive.ne', dif_neg (by simp)]

theorem rootStress_ae (initial : GeneratedWholeRestartCurrent nu) :
    rootStress initial =ᵐ[volume] rootOrdinary initial := by
  classical
  have regular := (ae_restrict_iff' measurableSet_Ioo).mp
    (ae_regularSet (receipt initial) (terminal initial) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2)
  filter_upwards [regular, (volume : Measure ℝ).ae_ne 0] with time regular nonzero
  by_cases inside : time ∈ Ioo (0 : ℝ) (terminal initial)
  · rw [rootStress, if_neg nonzero, dif_pos inside,
      NativeRecoveryJointCurrent.stress_regular initial ⟨time, inside⟩ (regular inside)]
    rfl
  · rw [rootStress, if_neg nonzero, dif_neg inside]

private theorem velocity_zero (initial : GeneratedWholeRestartCurrent nu) :
    velocity initial 0 = NativeCofinalMomentumAction.endpointVelocity initial := by
  rw [NativeRecoveryUnifiedCurrent.velocity, NativeRecoveryRowAction.velocity_on_interval (receipt initial) ⟨0, by norm_num⟩]
  apply lp.ext
  funext wave
  exact NativeRecoveryMomentumIntegral.source_recovery_zero initial wave

theorem root_action_row (initial : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : NonzeroIntegerWavevector) :
    NativeUnifiedRootActionFeed.action initial time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (projectedDivergenceCLM wave.1 (rootStress initial time wave.1) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • velocity initial time wave.1) := by
  classical
  by_cases zero : time = 0
  · subst time
    rw [NativeUnifiedRootActionFeed.action_zero, NativeUnifiedCofinalActionFeed.actionAt_row,
      rootStress_zero, velocity_zero]
    rfl
  · by_cases inside : time ∈ Ioo (0 : ℝ) (terminal initial)
    · rw [NativeUnifiedRootActionFeed.action_at_time initial ⟨time, inside⟩,
        NativeUnifiedRootActionFeed.interiorAction_row, rootStress_at_time initial ⟨time, inside⟩]
      rfl
    · rw [NativeUnifiedRootActionFeed.action, if_neg zero, dif_neg inside, rootStress, if_neg zero, dif_neg inside,
        NativeUnifiedRootActionFeed.ordinaryAction_row]
      have source := recoveryCurve_full (receipt initial) time
      change wholeVelocity (recoveryCurve (receipt initial) time) = velocity initial time at source
      rw [NativeMomentumIntegral.action, NativeMomentumIntegral.row, source]
      rfl

variable {current next : GeneratedWholeRestartCurrent nu}

def macroOrdinary (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) : NativeFluidStressFourierState :=
  quadraticFlux (wholeVelocity (step.physicalStageTrajectory time))

def macroStress (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) : NativeFluidStressFourierState :=
  if time ∈ Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance then
    rootStress current (time - wholeRestartVelocityAccumulationTime current)
  else macroOrdinary step time

def macroBudget (_step : GeneratedWholeRestartEndpointMacroStep nu current next) : ℝ :=
  max (rootBudget current) (‖puncturedWholeVelocityEuclideanState current.initialState‖ ^ 2)

theorem macroOrdinary_bound (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖macroOrdinary step time wave output input‖ ≤ ‖puncturedWholeVelocityEuclideanState current.initialState‖ ^ 2 := by
  have raw := quadraticFlux_norm_le_mass (wholeVelocity (step.physicalStageTrajectory time)) wave output input
  rw [wholeVelocity_mass] at raw
  exact raw.trans (pow_le_pow_left₀ (norm_nonneg _)
    (NativeNormControl.macro_stage_velocity_norm_le step
      (projIcc (0 : ℝ) step.clockAdvance step.clockAdvance_pos.le time)) 2)

theorem macroStress_bound (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖macroStress step time wave output input‖ ≤ macroBudget step := by
  unfold macroStress
  split_ifs
  · exact (rootStress_bound current _ wave output input).trans (le_max_left _ _)
  · exact (macroOrdinary_bound step time wave output input).trans (le_max_right _ _)


private theorem macro_recovery_velocity (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ)
    (inside : time ∈ Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance) :
    wholeVelocity (step.physicalStageTrajectory time) = velocity current (time - wholeRestartVelocityAccumulationTime current) := by
  have localTime : time - wholeRestartVelocityAccumulationTime current ∈ Icc (0 : ℝ) (recoveryTime step) := by
    rw [clock_split step] at inside
    constructor <;> linarith [inside.1, inside.2]
  have physical := NativeUnifiedMacroActionFeed.physical_recovery step (time - wholeRestartVelocityAccumulationTime current) localTime
  rw [add_sub_cancel] at physical
  rw [physical, recoveryCurve_full]
  rfl

theorem macro_action_row (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ)
    (wave : NonzeroIntegerWavevector) :
    NativeUnifiedMacroActionFeed.action step time wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      (projectedDivergenceCLM wave.1 (macroStress step time wave.1) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity (step.physicalStageTrajectory time) wave.1) := by
  unfold NativeUnifiedMacroActionFeed.action macroStress
  split_ifs with inside
  · rw [root_action_row, macro_recovery_velocity step time inside]
  · rw [NativeUnifiedMacroActionFeed.ordinary, NativeNegativeFourMomentum.actionState_apply,
      NativeMomentumIntegral.action, NativeMomentumIntegral.row]
    rfl

theorem macroStress_recovery (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) (recoveryTime step)) :
    macroStress step (wholeRestartVelocityAccumulationTime current + time) = rootStress current time := by
  have inRecovery : wholeRestartVelocityAccumulationTime current + time ∈
      Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance := by
    rw [clock_split step]
    constructor <;> linarith [inside.1, inside.2]
  rw [macroStress, if_pos inRecovery, add_sub_cancel_left]

theorem macroStress_cofinal (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    macroStress step (wholeRestartVelocityAccumulationTime current) = (sourceGeneratedCofinalStress current).stress := by
  simpa only [add_zero, rootStress_zero] using macroStress_recovery step 0 ⟨le_rfl, (recoveryTime_mem step).1⟩

theorem macroStress_zero (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    macroStress step 0 = quadraticFlux (wholeVelocity (puncturedWholeVelocityEuclideanState current.initialState)) := by
  rw [macroStress, if_neg (fun inside => not_le_of_gt (accumulation_positive step) inside.1), macroOrdinary]
  have start : step.physicalStageTrajectory 0 = puncturedWholeVelocityEuclideanState current.initialState :=
    (step.physicalStageTrajectory_eq_stage step.physicalStageZero).trans step.physicalStage_zero
  rw [start]

theorem macroStress_terminal (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    macroStress step step.clockAdvance = quadraticFlux (wholeVelocity (puncturedWholeVelocityEuclideanState next.initialState)) := by
  have physical := NativeUnifiedMacroActionFeed.physical_recovery step (recoveryTime step) ⟨(recoveryTime_mem step).1, le_rfl⟩
  have finish : step.physicalStageTrajectory step.clockAdvance = puncturedWholeVelocityEuclideanState next.initialState :=
    (step.physicalStageTrajectory_eq_stage step.physicalStageTerminal).trans step.physicalStage_terminal
  rw [← clock_split step, finish, NativeUnifiedMacroActionFeed.recoveryTime_eq_root] at physical
  rw [clock_split step, macroStress_recovery step _ ⟨(recoveryTime_mem step).1, le_rfl⟩,
    NativeUnifiedMacroActionFeed.recoveryTime_eq_root, rootStress_terminal, rootOrdinary, physical,
    recoveryCurve_full]
  rfl

theorem macroStress_ae (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    macroStress step =ᵐ[volume] macroOrdinary step := by
  have shifted := (measurePreserving_sub_right (volume : Measure ℝ) (wholeRestartVelocityAccumulationTime current)).quasiMeasurePreserving.ae_eq_comp
    (rootStress_ae current)
  filter_upwards [shifted] with time same
  dsimp only [Function.comp_def] at same
  by_cases inside : time ∈ Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance
  · rw [macroStress, if_pos inside, same, rootOrdinary, macroOrdinary, macro_recovery_velocity step time inside]
  · rw [macroStress, if_neg inside]

end
end SaturationMonoid.NavierStokes.NativeUnifiedStressSource
