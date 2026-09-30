import H0mework.Fock.RetainedReceiver.Value

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem maximum_advance (runtime : LivingRuntimeState process) (steps : Nat) :
    (maximumIndex (runtime.advance steps)).val = (maximumIndex runtime).val + steps := by
  rw [SourceCopyCurrentCoordinates.maximum_index_val, SourceGraphRecurrence.advance_depth,
    SourceCopyCurrentCoordinates.maximum_index_val]

def trajectory (runtime : LivingRuntimeState process) (initial : At runtime Key) (receipts : Nat → Key) (steps : Nat) :
    At (runtime.advance steps) Key :=
  reindex (SourceGraphRecurrence.advance_depth runtime steps).symm (maximum_advance runtime steps).symm
    (run (inventoryBound runtime) (maximumIndex runtime).val receipts initial steps)

theorem trajectory_zero (runtime : LivingRuntimeState process) (initial : At runtime Key) (receipts : Nat → Key) :
    trajectory runtime initial receipts 0 = initial := by
  rw [trajectory, run]
  rfl

theorem trajectory_next (runtime : LivingRuntimeState process) (initial : At runtime Key) (receipts : Nat → Key) (steps : Nat) :
    trajectory runtime initial receipts (steps + 1) =
      next (runtime.advance steps) (trajectory runtime initial receipts steps) (receipts steps) := by
  have target : (maximumIndex runtime).val + steps + 1 =
      (maximumIndex (runtime.advance steps).tick.next).val :=
    (maximum_advance runtime (steps + 1)).symm
  rw [trajectory, run, next, trajectory]
  rw [step_reindex (SourceGraphRecurrence.advance_depth runtime steps).symm
    (maximum_advance runtime steps).symm target, reindex_trans]
  rfl

theorem trajectory_native (runtime : LivingRuntimeState process) (initial : At runtime Key) (read : Nat → Key)
    (source : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) (steps : Nat) :
    (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps).native =
      SourceConditionalNativeObservers.generate read (inventoryBound (runtime.advance steps)) := by
  rw [trajectory, reindex_native, run_native _ _ initial read source steps]
  have transport (left right : Nat) (same : left = right) :
      cast (congrArg (SourceConditionalNativeObservers.State Key) same) (SourceConditionalNativeObservers.generate read left) =
        SourceConditionalNativeObservers.generate read right := by
    cases same
    rfl
  exact transport _ _ (SourceGraphRecurrence.advance_depth runtime steps).symm

theorem trajectory_keys (runtime : LivingRuntimeState process) (initial : At runtime Key) (read : Nat → Key)
    (source : initial.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) (steps : Nat) :
    (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps).keys =
      SourceUniformFibreVariance.outputs (inventoryBound (runtime.advance steps)) (fun actor => read actor.val) := by
  rw [trajectory, reindex_keys, run_keys _ _ initial read source steps, SourceGraphRecurrence.advance_depth]

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
