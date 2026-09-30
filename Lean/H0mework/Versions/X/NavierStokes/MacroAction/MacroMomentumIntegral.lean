import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryMomentumIntegral
import H0mework.Versions.X.NavierStokes.MomentumAction.MomentumIntegralSplice
import H0mework.Versions.X.NavierStokes.MomentumAction.OriginalMomentumIntegral

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeMacroMomentumIntegral

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeEndpointVelocityCarrier NativeRecoveryPhysical NativeRecoveryMomentumIntegral NativeMomentumIntegral

noncomputable section

variable {nu : Viscosity}
  {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

def recoveryCurve (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : ℝ) : WholeRestartVelocityEndpointState :=
  puncturedEuclideanize (NativeRecoveryRowAction.velocity receipt time)

theorem recoveryCurve_full (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : ℝ) : wholeVelocity (recoveryCurve receipt time) = NativeRecoveryRowAction.velocity receipt time :=
  wholeVelocity_puncturedEuclideanize _ (velocity_zero receipt time)

theorem recovery_writes (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) :
    WritesOn nu (recoveryCurve receipt) 1 := by
  intro wave
  have actions : (fun time => action nu (recoveryCurve receipt time) wave) =
      NativeRecoveryRowAction.rateRow receipt wave := by
    funext time
    simp only [action, row, recoveryCurve_full]
    rfl
  rw [actions]
  refine ⟨rate_integrable receipt wave, ?_⟩
  intro time inside
  simp only [row, recoveryCurve_full]
  rw [NativeRecoveryRowAction.velocity_on_interval receipt ⟨time, inside⟩,
    NativeRecoveryRowAction.velocity_on_interval receipt ⟨0, by norm_num⟩]
  exact velocity_sub_eq_integral receipt ⟨0, by norm_num⟩ ⟨time, inside⟩ inside.1 wave

variable {current next : GeneratedWholeRestartCurrent nu}

def recovery (step : GeneratedWholeRestartEndpointMacroStep nu current next) : ℝ → WholeRestartVelocityEndpointState :=
  recoveryCurve (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt current step.elapsedBounded)

def recoveryTime (step : GeneratedWholeRestartEndpointMacroStep nu current next) : ℝ :=
  (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice current step.elapsedBounded).time.1

theorem recoveryTime_mem (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    recoveryTime step ∈ Icc (0 : ℝ) 1 :=
  (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice current step.elapsedBounded).time.2

theorem recovery_writes_selected (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    WritesOn nu (recovery step) (recoveryTime step) :=
  (recovery_writes _).mono (recoveryTime_mem step).1 (recoveryTime_mem step).2

theorem clock_split (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    step.clockAdvance = wholeRestartVelocityAccumulationTime current + recoveryTime step := by
  rw [step.clockAdvance_eq_selectedAbsoluteTime]
  rfl

theorem accumulation_positive (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    0 < wholeRestartVelocityAccumulationTime current := by
  simpa only [elapsedTime_zero] using
    elapsedTime_lt_wholeRestartVelocityAccumulationTime current step.elapsedBounded 0

def earlyCurve (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : ℝ) : WholeRestartVelocityEndpointState :=
  sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice current step.elapsedBounded
    (projIcc (0 : ℝ) (wholeRestartVelocityAccumulationTime current + 1)
      (by linarith [accumulation_positive step]) time)

theorem physicalStage_reads_earlyCurve (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) step.clockAdvance) :
    step.physicalStageTrajectory time = earlyCurve step time := by
  rw [step.physicalStageTrajectory_eq_stage ⟨time, inside⟩]
  unfold earlyCurve
  have fullInside : time ∈ Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime current + 1) :=
    (step.physicalStageTime ⟨time, inside⟩).2
  rw [projIcc_of_mem _ fullInside]
  rfl

theorem earlyCurve_after (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (recoveryTime step)) :
    earlyCurve step (wholeRestartVelocityAccumulationTime current + time) = recovery step time := by
  have localInside : time ∈ Icc (0 : ℝ) 1 := ⟨inside.1, inside.2.trans (recoveryTime_mem step).2⟩
  have absoluteInside : wholeRestartVelocityAccumulationTime current + time ∈
      Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime current + 1) := by
    constructor <;> linarith [accumulation_positive step, localInside.1, localInside.2]
  rw [earlyCurve, projIcc_of_mem _ absoluteInside,
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge current step.elapsedBounded _
      (by change wholeRestartVelocityAccumulationTime current ≤ wholeRestartVelocityAccumulationTime current + time
          linarith [inside.1])]
  unfold sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath recovery recoveryCurve NativeRecoveryRowAction.velocity
  rw [projIcc_of_mem zero_le_one localInside]
  congr 2
  apply Subtype.ext
  simp [endpointAbsoluteToLocalTime]

theorem macro_writes_of_pre (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (pre : WritesOn nu (earlyCurve step) (wholeRestartVelocityAccumulationTime current)) :
    WritesOn nu step.physicalStageTrajectory step.clockAdvance := by
  have same : recovery step 0 = earlyCurve step (wholeRestartVelocityAccumulationTime current) := by
    simpa only [add_zero] using (earlyCurve_after step 0 ⟨le_rfl, (recoveryTime_mem step).1⟩).symm
  have joined := pre.splice (recovery_writes_selected step) (accumulation_positive step).le
    (recoveryTime_mem step).1 same
  rw [← clock_split step] at joined
  apply joined.congr step.clockAdvance_pos.le
  intro time inside
  rw [physicalStage_reads_earlyCurve step time inside]
  by_cases before : time ≤ wholeRestartVelocityAccumulationTime current
  · rw [endpointSplice_of_le _ _ _ _ before]
  · have after : wholeRestartVelocityAccumulationTime current < time := lt_of_not_ge before
    rw [endpointSplice_of_lt _ _ _ _ after]
    have localInside : time - wholeRestartVelocityAccumulationTime current ∈ Icc (0 : ℝ) (recoveryTime step) := by
      rw [clock_split step] at inside
      constructor <;> linarith [inside.2]
    simpa only [add_sub_cancel] using earlyCurve_after step _ localInside

theorem stage_writes (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    WritesOn nu step.physicalStageTrajectory step.clockAdvance :=
  macro_writes_of_pre step (NativeOriginalMomentumIntegral.pre_accumulation_write current step.elapsedBounded)

end
end SaturationMonoid.NavierStokes.NativeMacroMomentumIntegral
