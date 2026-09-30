import H0mework.NavierStokes.NormControl.Splice
import H0mework.NavierStokes.WholeReceipt.Global
import H0mework.NavierStokes.Accumulation.NativeTurbulenceLaw

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeNormControl

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}

theorem old_trajectory_velocity_norm_le (trajectory : GeneratedWholeGlobalPhysicalTrajectory initial)
    (time : ℝ) (nonneg : 0 ≤ time) :
    ‖puncturedWholeVelocityEuclideanState (trajectory.physicalPath time)‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ := by
  have positive : 0 < time + 1 := by linarith
  let point : Icc (0 : ℝ) (time + 1) := ⟨time, nonneg, by linarith⟩
  rw [← WholeGlobalReceipt.ofTrajectory_path trajectory (time + 1) positive point]
  exact receipt_velocity_norm_le ((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt _ positive) point

theorem recovery_receipt_velocity_norm_le {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (time : Icc (0 : ℝ) law.recovery.next.duration) :
    ‖puncturedWholeVelocityEuclideanState (law.recovery.next.receipt.wholePath time)‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ :=
  (receipt_velocity_norm_le law.recovery.next.receipt time).trans
    (macro_next_velocity_norm_le law.recovery.step)

/-- This property reads the original sealed answer. Its revised clause controls
the actual stage and the literal recovery receipt returned by that answer. -/
def BoundaryVelocityControlled (answer : SourceGeneratedNativeBoundaryReachabilityAnswerAt initial) : Prop :=
  answer.fold
    (fun _ trajectory => ∀ time : ℝ, 0 ≤ time →
      ‖puncturedWholeVelocityEuclideanState (trajectory.physicalPath time)‖ ≤
        ‖puncturedWholeVelocityEuclideanState initial.initialState‖)
    (fun _ _ law =>
      (∀ time : Icc (0 : ℝ) law.recovery.step.clockAdvance,
        ‖law.recovery.step.physicalStage time‖ ≤
          ‖puncturedWholeVelocityEuclideanState initial.initialState‖) ∧
      (∀ time : Icc (0 : ℝ) law.recovery.next.duration,
        ‖puncturedWholeVelocityEuclideanState (law.recovery.next.receipt.wholePath time)‖ ≤
          ‖puncturedWholeVelocityEuclideanState initial.initialState‖))

theorem boundary_velocity_control (answer : SourceGeneratedNativeBoundaryReachabilityAnswerAt initial) :
    BoundaryVelocityControlled answer := by
  unfold BoundaryVelocityControlled SourceGeneratedNativeBoundaryReachabilityAnswerAt.fold
  split
  · exact old_trajectory_velocity_norm_le _
  · exact ⟨macro_stage_velocity_norm_le _, recovery_receipt_velocity_norm_le _⟩

/-- The public producer's exact answer inherits physical norm control without
a caller branch, elapsed bound, zero defect, or replacement path. -/
theorem source_generated_boundary_velocity_control (initial : GeneratedWholeRestartCurrent nu) :
    BoundaryVelocityControlled (sourceGeneratedNativeBoundaryReachabilityAnswer initial) :=
  boundary_velocity_control _

end
end SaturationMonoid.NavierStokes.NativeNormControl
