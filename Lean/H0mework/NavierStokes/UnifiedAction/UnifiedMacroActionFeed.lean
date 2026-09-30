import H0mework.NavierStokes.UnifiedAction.UnifiedRootActionFeed
import H0mework.NavierStokes.NormControl.Splice

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedMacroActionFeed

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin
open NativeEndpointVelocityCarrier NativeNegativeFourMomentum NativeMacroMomentumIntegral

noncomputable section

variable {nu : Viscosity} {current next : GeneratedWholeRestartCurrent nu}

theorem recovery_eq_root (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    recovery step = recoveryCurve (NativeRecoveryUnifiedCurrent.receipt current) := by
  unfold recovery NativeRecoveryUnifiedCurrent.receipt
  unfold sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
  unfold sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
  rw [sourceGeneratedWholeRestartVelocityEndpointLedger_toCore_eq_nativeTemporal current step.elapsedBounded]

theorem recoveryTime_eq_root (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    recoveryTime step = NativeRecoveryUnifiedCurrent.terminal current := by
  unfold recoveryTime NativeRecoveryUnifiedCurrent.terminal
  unfold sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice sourceGeneratedNativeTemporalPositiveTimeH1Slice
  unfold sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
  rw [sourceGeneratedWholeRestartVelocityEndpointLedger_toCore_eq_nativeTemporal current step.elapsedBounded]

theorem physical_recovery (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (recoveryTime step)) :
    step.physicalStageTrajectory (wholeRestartVelocityAccumulationTime current + time) =
      recoveryCurve (NativeRecoveryUnifiedCurrent.receipt current) time := by
  rw [physicalStage_reads_earlyCurve step _ (by
    rw [clock_split step]
    constructor <;> linarith [accumulation_positive step, inside.1, inside.2]),
    earlyCurve_after step time inside, recovery_eq_root]

private theorem stage_zero (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    step.physicalStageTrajectory 0 = puncturedWholeVelocityEuclideanState current.initialState :=
  (step.physicalStageTrajectory_eq_stage step.physicalStageZero).trans step.physicalStage_zero

private theorem stage_terminal (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    step.physicalStageTrajectory step.clockAdvance = puncturedWholeVelocityEuclideanState next.initialState :=
  (step.physicalStageTrajectory_eq_stage step.physicalStageTerminal).trans step.physicalStage_terminal

def ordinary (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) : WholeRestartVelocityEndpointState :=
  actionState nu (step.physicalStageTrajectory time)

def action (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) : WholeRestartVelocityEndpointState :=
  if time ∈ Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance then
    NativeUnifiedRootActionFeed.action current (time - wholeRestartVelocityAccumulationTime current)
  else ordinary step time

def ordinaryBudget (current : GeneratedWholeRestartCurrent nu) : ℝ :=
  actionBudget nu ‖puncturedWholeVelocityEuclideanState current.initialState‖

def budget (_step : GeneratedWholeRestartEndpointMacroStep nu current next) : ℝ :=
  max (ordinaryBudget current)
    (max (NativeUnifiedRootActionFeed.budget current) (NativeUnifiedCofinalActionFeed.budget current))

theorem ordinary_bound (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) :
    ‖ordinary step time‖ ≤ ordinaryBudget current :=
  actionState_norm_le nu _ _ (NativeNormControl.macro_stage_velocity_norm_le step
    (projIcc (0 : ℝ) step.clockAdvance step.clockAdvance_pos.le time))

theorem action_bound (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) :
    ‖action step time‖ ≤ budget step := by
  unfold action
  split_ifs
  · exact (NativeUnifiedRootActionFeed.action_bound current _).trans (le_max_right _ _)
  · exact (ordinary_bound step time).trans (le_max_left _ _)

theorem action_before (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : ℝ) (before : time < wholeRestartVelocityAccumulationTime current) :
    action step time = ordinary step time := by
  rw [action, if_neg (fun inside => not_le_of_gt before inside.1)]

theorem action_recovery (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (recoveryTime step)) :
    action step (wholeRestartVelocityAccumulationTime current + time) = NativeUnifiedRootActionFeed.action current time := by
  have inRecovery : wholeRestartVelocityAccumulationTime current + time ∈
      Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance := by
    rw [clock_split step]
    constructor <;> linarith [inside.1, inside.2]
  rw [action, if_pos inRecovery, add_sub_cancel_left]

theorem action_cofinal (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    action step (wholeRestartVelocityAccumulationTime current) = NativeUnifiedCofinalActionFeed.actionAt current := by
  simpa only [add_zero, NativeUnifiedRootActionFeed.action_zero] using
    action_recovery step 0 ⟨le_rfl, (recoveryTime_mem step).1⟩

theorem action_zero (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    action step 0 = actionState nu (puncturedWholeVelocityEuclideanState current.initialState) := by
  rw [action_before step 0 (accumulation_positive step), ordinary,
    stage_zero]

theorem action_terminal (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    action step step.clockAdvance = actionState nu (puncturedWholeVelocityEuclideanState next.initialState) := by
  have terminalPositive : 0 < NativeRecoveryUnifiedCurrent.terminal current :=
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice current).time_pos
  have ordinaryAtTerminal : NativeUnifiedRootActionFeed.action current (recoveryTime step) =
      NativeUnifiedRootActionFeed.ordinaryAction current (recoveryTime step) := by
    rw [recoveryTime_eq_root, NativeUnifiedRootActionFeed.action, if_neg terminalPositive.ne',
      dif_neg (by simp)]
  have physical := physical_recovery step (recoveryTime step) ⟨(recoveryTime_mem step).1, le_rfl⟩
  rw [← clock_split step, stage_terminal] at physical
  rw [clock_split step, action_recovery step _ ⟨(recoveryTime_mem step).1, le_rfl⟩, ordinaryAtTerminal,
    NativeUnifiedRootActionFeed.ordinaryAction, ← physical]

theorem action_ae (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    action step =ᵐ[volume] ordinary step := by
  have shifted := (measurePreserving_sub_right (volume : Measure ℝ) (wholeRestartVelocityAccumulationTime current)).quasiMeasurePreserving.ae_eq_comp
    (NativeUnifiedRootActionFeed.action_ae_ordinary current)
  filter_upwards [shifted] with time same
  dsimp only [Function.comp_def] at same
  by_cases inRecovery : time ∈ Icc (wholeRestartVelocityAccumulationTime current) step.clockAdvance
  · have localTime : time - wholeRestartVelocityAccumulationTime current ∈ Icc (0 : ℝ) (recoveryTime step) := by
      rw [clock_split step] at inRecovery
      constructor <;> linarith [inRecovery.1, inRecovery.2]
    have physical := physical_recovery step (time - wholeRestartVelocityAccumulationTime current) localTime
    rw [add_sub_cancel] at physical
    rw [action, if_pos inRecovery, same, NativeUnifiedRootActionFeed.ordinaryAction, ordinary, physical]
  · rw [action, if_neg inRecovery]

private theorem ordinary_intervalIntegrable (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    IntervalIntegrable (ordinary step) volume 0 step.clockAdvance := by
  have coordinate (wave : NonzeroIntegerWavevector) : AEStronglyMeasurable
      (fun time => ordinary step time wave) (volume.restrict (Icc (0 : ℝ) step.clockAdvance)) := by
    have raw := (intervalIntegrable_iff_integrableOn_Icc_of_le step.clockAdvance_pos.le).mp
      (stage_writes step wave.1).1
    exact (weightedRowCLM wave.1).continuous.comp_aestronglyMeasurable raw.aestronglyMeasurable
  let partialSum (observed : Finset NonzeroIntegerWavevector) (time : ℝ) : WholeRestartVelocityEndpointState :=
    ∑ wave ∈ observed, lp.single 2 wave (ordinary step time wave)
  have partialMeasurable (observed : Finset NonzeroIntegerWavevector) :
      AEStronglyMeasurable (partialSum observed) (volume.restrict (Icc (0 : ℝ) step.clockAdvance)) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
      |>.comp_aestronglyMeasurable (coordinate wave)
  have whole : AEStronglyMeasurable (ordinary step) (volume.restrict (Icc (0 : ℝ) step.clockAdvance)) := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset NonzeroIntegerWavevector)) partialMeasurable
    exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (ordinary step time)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le step.clockAdvance_pos.le).mpr
  exact IntegrableOn.of_bound (isCompact_Icc.measure_lt_top (μ := volume)) whole (ordinaryBudget current)
    (Eventually.of_forall (ordinary_bound step))

theorem action_intervalIntegrable (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    IntervalIntegrable (action step) volume 0 step.clockAdvance :=
  (ordinary_intervalIntegrable step).congr_ae (ae_restrict_of_ae (action_ae step).symm)

theorem action_Linfty (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    MemLp (action step) ∞ (volume.restrict (Icc (0 : ℝ) step.clockAdvance)) ∧
      eLpNorm (action step) ∞ (volume.restrict (Icc (0 : ℝ) step.clockAdvance)) ≤ ENNReal.ofReal (budget step) := by
  have measurable := ((intervalIntegrable_iff_integrableOn_Icc_of_le step.clockAdvance_pos.le).mp
    (action_intervalIntegrable step)).aestronglyMeasurable
  have bounded : ∀ᵐ time ∂volume.restrict (Icc (0 : ℝ) step.clockAdvance), ‖action step time‖ ≤ budget step :=
    Eventually.of_forall (action_bound step)
  exact ⟨memLp_top_of_bound measurable _ bounded, eLpNormEssSup_le_of_ae_bound bounded⟩

theorem integral_at_time (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) step.clockAdvance) :
    embed (step.physicalStageTrajectory time) - embed (step.physicalStageTrajectory 0) = ∫ actual in 0..time, action step actual := by
  rw [intervalIntegral.integral_congr_ae ((action_ae step).mono fun _ same _ => same)]
  have integrable := (ordinary_intervalIntegrable step).mono_set (by
    rw [uIcc_of_le inside.1, uIcc_of_le step.clockAdvance_pos.le]
    exact Icc_subset_Icc le_rfl inside.2)
  apply lp.ext
  funext wave
  change embed (step.physicalStageTrajectory time) wave - embed (step.physicalStageTrajectory 0) wave =
    (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)
      (∫ actual in 0..time, ordinary step actual)
  rw [← (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).intervalIntegral_comp_comm integrable]
  change embed (step.physicalStageTrajectory time) wave - embed (step.physicalStageTrajectory 0) wave =
    ∫ actual in 0..time, weightedRowCLM wave.1 (NativeMomentumIntegral.action nu (step.physicalStageTrajectory actual) wave.1)
  rw [(weightedRowCLM wave.1).intervalIntegral_comp_comm ((stage_writes step).mono inside.1 inside.2 wave.1).1]
  have raw := (stage_writes step wave.1).2 time inside
  rw [← raw, map_sub, weightedRowCLM_row, weightedRowCLM_row]

theorem source_integral (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    embed (puncturedWholeVelocityEuclideanState next.initialState) -
      embed (puncturedWholeVelocityEuclideanState current.initialState) = ∫ time in 0..step.clockAdvance, action step time := by
  have written := integral_at_time step step.clockAdvance ⟨step.clockAdvance_pos.le, le_rfl⟩
  rw [stage_terminal, stage_zero] at written
  exact written

end
end SaturationMonoid.NavierStokes.NativeUnifiedMacroActionFeed
