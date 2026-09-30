import H0mework.Versions.X.Fock.HistoryConditional.MinimumWindowErrorSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumWindowError

open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem action_orthogonal (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (target : SourceJointClockGraph.Carrier) (error : Window runtime index) :
    ⟪SourceJointClockGraph.action (readout runtime index nonunit steps error),
      SourceJointClockGraph.action (residual runtime index steps target)⟫_ℂ = 0 := by
  have massZero := congrArg (fun value : SourceCopyCurrentCoordinates.Coordinates runtime index steps => value.2.1)
    (SourceCopyCurrentCoordinates.residual_source runtime index steps target)
  have clockZero := congrArg (fun value : SourceCopyCurrentCoordinates.Coordinates runtime index steps => value.2.2)
    (SourceCopyCurrentCoordinates.residual_source runtime index steps target)
  change SourceMassCompletion.massRead (SourceJointClockGraph.joint (residual runtime index steps target)) = 0 at massZero
  change SourceJointClockGraph.clock (residual runtime index steps target) = 0 at clockZero
  have jointZero := readout_orthogonal runtime index nonunit steps target error
  rw [WithLp.prod_inner_apply] at jointZero
  change ⟪SourceJointClockGraph.joint (readout runtime index nonunit steps error),
    SourceJointClockGraph.joint (residual runtime index steps target)⟫_ℂ +
    ⟪SourceJointClockGraph.clock (readout runtime index nonunit steps error),
      SourceJointClockGraph.clock (residual runtime index steps target)⟫_ℂ = 0 at jointZero
  rw [clockZero, inner_zero_right, add_zero] at jointZero
  rw [SourceJointClockGraph.action_apply, SourceJointClockGraph.action_apply, WithLp.prod_inner_apply]
  change ⟪SourceMassCompletion.action (SourceJointClockGraph.joint (readout runtime index nonunit steps error)),
    SourceMassCompletion.action (SourceJointClockGraph.joint (residual runtime index steps target))⟫_ℂ +
    ⟪SourceJointClockGraph.clock (readout runtime index nonunit steps error) +
        SourceMassCompletion.massRead (SourceJointClockGraph.joint (readout runtime index nonunit steps error)),
      SourceJointClockGraph.clock (residual runtime index steps target) +
        SourceMassCompletion.massRead (SourceJointClockGraph.joint (residual runtime index steps target))⟫_ℂ = 0
  rw [LinearIsometry.inner_map_map, clockZero, massZero, add_zero, inner_zero_right, add_zero]
  exact jointZero

theorem action_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (target : SourceJointClockGraph.Carrier) (error : Window runtime (maximumIndex runtime)) :
    ‖SourceJointClockGraph.action target - SourceJointClockGraph.action
      (readout runtime (maximumIndex runtime) nonunit 0
        (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) target + error))‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 target‖ ^ 2 +
        ‖SourceJointClockGraph.action (readout runtime (maximumIndex runtime) nonunit 0 error)‖ ^ 2 := by
  rw [← map_sub, error_vector, map_add, map_neg, norm_add_sq (𝕜 := ℂ), inner_neg_left,
    action_orthogonal, neg_zero, RCLike.zero_re, mul_zero, add_zero, norm_neg,
    SourceCopySharedNext.tail_time_energy]
  exact add_comm _ _

theorem step_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (target : SourceJointClockGraph.Carrier) (error : Window runtime (maximumIndex runtime)) :
    ‖SourceJointClockGraph.action target -
      readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
        (SourceMinimumSharedNext.step runtime nonunit
          (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) target + error))‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 target‖ ^ 2 +
        ‖SourceJointClockGraph.action (readout runtime (maximumIndex runtime) nonunit 0 error)‖ ^ 2 := by
  have effect :
      readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
        (SourceMinimumSharedNext.step runtime nonunit
          (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) target + error)) =
      SourceJointClockGraph.action (readout runtime (maximumIndex runtime) nonunit 0
        (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) target + error)) := by
    dsimp only [readout, LinearMap.comp_apply]
    exact SourceMinimumSharedNext.step_realize runtime nonunit _
  exact (congrArg (fun value => ‖SourceJointClockGraph.action target - value‖ ^ 2) effect).trans
    (action_error runtime nonunit target error)

end
end SourceMinimumWindowError
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
