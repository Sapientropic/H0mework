import H0mework.Versions.X.NavierStokes.NormControl.Physical
import H0mework.NavierStokes.VelocityEndpoint.MacroPhysicalStage

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeNormControl

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

noncomputable section

variable {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)

theorem prefix_velocity_norm_le_initial (length : Nat)
    (time : Icc (0 : ℝ) (elapsedTime initial (length + 1))) :
    ‖puncturedWholeVelocityEuclideanState (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time.1)‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ :=
  receipt_velocity_norm_le (WholePrefixReceipt.receipt initial length) time

theorem pre_velocity_norm_le_initial
    (bounded : BddAbove (range (elapsedTime initial)))
    (time : Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) :
    ‖wholeRestartBoundedPreAccumulationVelocityTrajectory initial bounded time‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ := by
  let cover := wholeRestartPreAccumulationCoverIndex initial bounded time
  have timeLe : time.1 ≤ elapsedTime initial (cover + 1) :=
    (wholeRestartPreAccumulationCoverIndex_spec initial bounded time).le.trans
      ((elapsedTime_strictMono initial).monotone (Nat.le_succ cover))
  unfold wholeRestartBoundedPreAccumulationVelocityTrajectory
  rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix initial bounded time (cover + 1) timeLe]
  exact prefix_velocity_norm_le_initial initial cover ⟨time.1, time.2.1, timeLe⟩

theorem absolute_endpoint_norm_le_initial
    (bounded : BddAbove (range (elapsedTime initial)))
    (time : Icc (wholeRestartVelocityAccumulationTime initial) (wholeRestartVelocityAccumulationTime initial + 1)) :
    ‖sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath initial bounded time‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ := by
  unfold sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath
  rw [sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath_eq_nativeTemporal initial bounded]
  exact endpoint_physical_norm_le_initial initial
    (endpointAbsoluteToLocalTime (wholeRestartVelocityAccumulationTime initial) time)

theorem splice_velocity_norm_le_initial
    (bounded : BddAbove (range (elapsedTime initial)))
    (time : Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime initial + 1)) :
    ‖sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice initial bounded time‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ := by
  by_cases before : time.1 < wholeRestartVelocityAccumulationTime initial
  · rw [sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt initial bounded time before]
    exact pre_velocity_norm_le_initial initial bounded _
  · rw [sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge initial bounded time (le_of_not_gt before)]
    exact absolute_endpoint_norm_le_initial initial bounded _

theorem macro_stage_velocity_norm_le {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : Icc (0 : ℝ) step.clockAdvance) :
    ‖step.physicalStage time‖ ≤ ‖puncturedWholeVelocityEuclideanState current.initialState‖ :=
  splice_velocity_norm_le_initial current step.elapsedBounded (step.physicalStageTime time)

theorem macro_next_velocity_norm_le {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    ‖puncturedWholeVelocityEuclideanState next.initialState‖ ≤
      ‖puncturedWholeVelocityEuclideanState current.initialState‖ := by
  rw [← step.physicalStage_terminal]
  exact macro_stage_velocity_norm_le step step.physicalStageTerminal

end
end SaturationMonoid.NavierStokes.NativeNormControl
