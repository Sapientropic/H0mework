import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesJoint
import H0mework.Versions.X.Fock.CopyGraph.SharedNextData

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyCurrentCoordinates (maximumIndex retained residual sourceRead Coordinates)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTimeModel (time hilbert mass)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem cutoff_growth (runtime : LivingRuntimeState process) :
    cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 =
      cutoff runtime (maximumIndex runtime) 0 + 2 * inventoryBound runtime + 3 := by
  have old := SourceCopyCurrentCoordinates.maximum_cutoff runtime
  have newer := SourceCopyCurrentCoordinates.maximum_cutoff runtime.tick.next
  have depth := SourceGraphRecurrence.advance_depth runtime 1
  change inventoryBound runtime.tick.next = inventoryBound runtime + 1 at depth
  rw [depth] at newer
  nlinarith only [old, newer]

theorem old_time_retained_tail_zero (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    residual runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceJointClockGraph.action (retained runtime (maximumIndex runtime) 0 target)) = 0 := by
  apply (SourceCopyCurrentCoordinates.complete_fibre runtime.tick.next (maximumIndex runtime.tick.next) 0 _ 0).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceCopyCurrentCoordinates.residual_source, map_zero]
  · intro coordinate beyond
    rw [SourceCopyCurrentCoordinates.residual_outside _ _ _ _ _ beyond]
    have growth := cutoff_growth runtime
    have shifted := SourceCopyTimeModel.time_hilbert_add 1 (retained runtime (maximumIndex runtime) 0 target) (coordinate - 1)
    rw [show coordinate - 1 + 1 = coordinate by omega] at shifted
    change hilbert (time 1 (retained runtime (maximumIndex runtime) 0 target)) coordinate = 0
    apply shifted.trans
    change SourceCopyCurrentCoordinates.hilbertLift runtime (maximumIndex runtime) 0
      (sourceRead runtime (maximumIndex runtime) 0 target).1 (coordinate - 1) = 0
    exact SourceCopyCurrentCoordinates.hilbert_lift_outside runtime (maximumIndex runtime) 0 _ _ (by omega)

theorem whole_tail_next (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target)) =
      residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) := by
  change residual runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (target - retained runtime (maximumIndex runtime) 0 target)) = _
  rw [map_sub, map_sub, old_time_retained_tail_zero, sub_zero]

def flow (runtime : LivingRuntimeState process) : SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (retained runtime.tick.next (maximumIndex runtime.tick.next) 0).comp
    (SourceJointClockGraph.action.toLinearMap.comp (residual runtime (maximumIndex runtime) 0))

theorem flow_partition (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    flow runtime target + residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) =
      SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target) := by
  have source := SourceCopyCurrentCoordinates.reconstruction runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target))
  rw [whole_tail_next] at source
  exact source

theorem next_reconstruction (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    retained runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) =
      SourceJointClockGraph.action (retained runtime (maximumIndex runtime) 0 target) + flow runtime target := by
  have kept := SourceCopyCurrentCoordinates.reconstruction runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (retained runtime (maximumIndex runtime) 0 target))
  rw [old_time_retained_tail_zero, add_zero] at kept
  have source := congrArg (fun value => retained runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action value))
    (SourceCopyCurrentCoordinates.reconstruction runtime (maximumIndex runtime) 0 target)
  rw [map_add, map_add, kept] at source
  exact source.symm

theorem tail_time_energy (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    ‖SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target)‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 target‖ ^ 2 := by
  have mzero := congrArg (fun value : Coordinates runtime (maximumIndex runtime) 0 => value.2.1)
    (SourceCopyCurrentCoordinates.residual_source runtime (maximumIndex runtime) 0 target)
  change mass (residual runtime (maximumIndex runtime) 0 target) = 0 at mzero
  rw [SourceJointClockGraph.action_energy]
  change ‖residual runtime (maximumIndex runtime) 0 target‖ ^ 2 + ‖mass (residual runtime (maximumIndex runtime) 0 target)‖ ^ 2 +
    2 * (inner ℂ (SourceJointClockGraph.clock (residual runtime (maximumIndex runtime) 0 target)) (mass (residual runtime (maximumIndex runtime) 0 target))).re = _
  rw [mzero, norm_zero, zero_pow (by decide : 2 ≠ 0), inner_zero_right, Complex.zero_re, mul_zero, add_zero, add_zero]

theorem flow_budget (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    ‖flow runtime target‖ ^ 2 + ‖residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 target‖ ^ 2 := by
  rw [show flow runtime target = retained runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target)) from rfl]
  have source := SourceCopyCurrentCoordinates.energy runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target))
  rw [whole_tail_next, tail_time_energy] at source
  exact source

end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
