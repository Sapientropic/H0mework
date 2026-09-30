import H0mework.Fock.CopyGraph.NativeModelStepSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyFutureCoordinates (retained residual sourceRead Coordinates)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem old_time_retained_tail_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index (steps + 1) (SourceJointClockGraph.action (retained runtime index steps target)) = 0 := by
  apply (SourceCopyFutureCoordinates.complete_fibre runtime index (steps + 1) _ 0).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceCopyFutureCoordinates.residual_source, map_zero]
  · intro coordinate beyond
    rw [SourceCopyFutureCoordinates.residual_outside _ _ _ _ _ beyond]
    change SourceCopyRecordedRecurrence.cutoff runtime index (steps + 2) < coordinate at beyond
    have address := SourceCopyFutureUpdate.cutoff_step runtime index steps
    have positive := SourceCopyProgram.scale_pos (inventoryBound runtime) index
    have shifted := SourceCopyTimeModel.time_hilbert_add 1 (retained runtime index steps target) (coordinate - 1)
    rw [show coordinate - 1 + 1 = coordinate by omega] at shifted
    change hilbert (time 1 (retained runtime index steps target)) coordinate = 0
    apply shifted.trans
    change SourceCopyFutureCoordinates.hilbertLift runtime index steps (sourceRead runtime index steps target).1 (coordinate - 1) = 0
    exact SourceCopyFutureCoordinates.hilbert_lift_outside runtime index steps _ _ (by omega)

theorem whole_tail_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index (steps + 1) (SourceJointClockGraph.action (residual runtime index steps target)) =
      residual runtime index (steps + 1) (SourceJointClockGraph.action target) := by
  change residual runtime index (steps + 1) (SourceJointClockGraph.action (target - retained runtime index steps target)) = _
  rw [map_sub, map_sub, old_time_retained_tail_zero, sub_zero]

def flow (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (retained runtime index (steps + 1)).comp (SourceJointClockGraph.action.toLinearMap.comp (residual runtime index steps))

theorem flow_partition (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    flow runtime index steps target + residual runtime index (steps + 1) (SourceJointClockGraph.action target) =
      SourceJointClockGraph.action (residual runtime index steps target) := by
  have source := SourceCopyFutureCoordinates.reconstruction runtime index (steps + 1) (SourceJointClockGraph.action (residual runtime index steps target))
  rw [whole_tail_next] at source
  exact source

theorem next_reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    retained runtime index (steps + 1) (SourceJointClockGraph.action target) =
      SourceJointClockGraph.action (retained runtime index steps target) + flow runtime index steps target := by
  have kept := SourceCopyFutureCoordinates.reconstruction runtime index (steps + 1) (SourceJointClockGraph.action (retained runtime index steps target))
  rw [old_time_retained_tail_zero, add_zero] at kept
  have source := congrArg (fun value => retained runtime index (steps + 1) (SourceJointClockGraph.action value))
    (SourceCopyFutureCoordinates.reconstruction runtime index steps target)
  rw [map_add, map_add, kept] at source
  exact source.symm

theorem tail_time_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖SourceJointClockGraph.action (residual runtime index steps target)‖ ^ 2 = ‖residual runtime index steps target‖ ^ 2 := by
  have mzero := congrArg (fun value : Coordinates runtime index steps => value.2.1)
    (SourceCopyFutureCoordinates.residual_source runtime index steps target)
  change mass (residual runtime index steps target) = 0 at mzero
  rw [SourceJointClockGraph.action_energy]
  change ‖residual runtime index steps target‖ ^ 2 + ‖mass (residual runtime index steps target)‖ ^ 2 +
    2 * (inner ℂ (SourceJointClockGraph.clock (residual runtime index steps target)) (mass (residual runtime index steps target))).re = _
  rw [mzero, norm_zero, zero_pow (by decide : 2 ≠ 0), inner_zero_right, Complex.zero_re, mul_zero, add_zero, add_zero]

theorem flow_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖flow runtime index steps target‖ ^ 2 + ‖residual runtime index (steps + 1) (SourceJointClockGraph.action target)‖ ^ 2 =
      ‖residual runtime index steps target‖ ^ 2 := by
  have source := SourceCopyFutureCoordinates.energy runtime index (steps + 1) (SourceJointClockGraph.action (residual runtime index steps target))
  rw [whole_tail_next, tail_time_energy] at source
  exact source

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
