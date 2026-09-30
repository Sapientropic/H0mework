import H0mework.Fock.CopyGraph.FutureUpdateModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureUpdate

open SourceCopyProgram (Index)
open SourceCopyFutureCoordinates (retained residual realize sourceRead Coordinates)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem old_retained_tail_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index (steps + 1) (retained runtime index steps target) = 0 := by
  apply (SourceCopyFutureCoordinates.complete_fibre runtime index (steps + 1) _ 0).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceCopyFutureCoordinates.residual_source, map_zero]
  · intro coordinate beyond
    rw [SourceCopyFutureCoordinates.residual_outside _ _ _ _ _ beyond]
    change SourceCopyFutureCoordinates.hilbertLift runtime index steps (sourceRead runtime index steps target).1 coordinate = 0
    apply SourceCopyFutureCoordinates.hilbert_lift_outside
    have address := cutoff_step runtime index steps
    change SourceCopyRecordedRecurrence.cutoff runtime index (steps + 2) < coordinate at beyond
    omega

theorem whole_tail_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index (steps + 1) (residual runtime index steps target) = residual runtime index (steps + 1) target := by
  change residual runtime index (steps + 1) (target - retained runtime index steps target) = _
  rw [map_sub, old_retained_tail_zero, sub_zero]

def block (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  (retained runtime index (steps + 1)).comp (residual runtime index steps)

theorem block_partition (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    block runtime index steps target + residual runtime index (steps + 1) target = residual runtime index steps target := by
  have source := SourceCopyFutureCoordinates.reconstruction runtime index (steps + 1) (residual runtime index steps target)
  rw [whole_tail_step] at source
  exact source

theorem retained_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    retained runtime index (steps + 1) target = retained runtime index steps target + block runtime index steps target := by
  have kept := SourceCopyFutureCoordinates.reconstruction runtime index (steps + 1) (retained runtime index steps target)
  rw [old_retained_tail_zero, add_zero] at kept
  have source := congrArg (retained runtime index (steps + 1)) (SourceCopyFutureCoordinates.reconstruction runtime index steps target)
  rw [map_add, kept] at source
  exact source.symm

theorem block_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖block runtime index steps target‖ ^ 2 + ‖residual runtime index (steps + 1) target‖ ^ 2 = ‖residual runtime index steps target‖ ^ 2 := by
  have source := SourceCopyFutureCoordinates.energy runtime index (steps + 1) (residual runtime index steps target)
  rw [whole_tail_step] at source
  exact source

def gain (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (previous : Coordinates runtime index steps) (observed : Samples runtime index) : SourceJointClockGraph.Carrier :=
  realize runtime index (steps + 1) (update runtime index steps previous observed) - realize runtime index steps previous

theorem gain_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    gain runtime index steps (sourceRead runtime index steps target) (samples runtime index steps target) = block runtime index steps target := by
  rw [gain, update_source]
  change retained runtime index (steps + 1) target - retained runtime index steps target = _
  rw [retained_step]
  abel

end
end SourceCopyFutureUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
