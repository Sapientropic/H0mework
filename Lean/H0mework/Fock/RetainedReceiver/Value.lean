import H0mework.Fock.RetainedReceiver.Transport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev At (runtime : LivingRuntimeState process) (Key : Type*) :=
  Frame Key (inventoryBound runtime) (maximumIndex runtime).val

def next (runtime : LivingRuntimeState process) (frame : At runtime Key) (added : Key) : At runtime.tick.next Key :=
  reindex (SourceActualImageStep.next_bound runtime).symm rfl
    (step (inventoryBound runtime) (maximumIndex runtime).val (maximumIndex runtime.tick.next).val frame added)

def value (runtime : LivingRuntimeState process) (frame : At runtime Key) (key : Key) : SourceJointClockGraph.Carrier :=
  SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
    (rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key)

theorem next_value (runtime : LivingRuntimeState process) (frame : At runtime Key) (added key : Key) :
    value runtime.tick.next (next runtime frame added) key =
      if key = added then value runtime frame key +
        ((((frame.native key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) • (SourceConditionalInventory.born (inventoryBound runtime) - value runtime frame key)
      else value runtime frame key := by
  rw [value, next, reindex_raw, step_raw]
  change SourceReceivedConditionalStep.completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceReceivedConditionalStep.nextData runtime (maximumIndex runtime) (frame.native key).1
      (decide (key = added)) (rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key)) = _
  have paid := SourceReceivedConditionalStep.next_value_source runtime (maximumIndex runtime) (frame.native key).1
    (decide (key = added)) (rawAt (inventoryBound runtime) (maximumIndex runtime).val frame key)
  simpa only [value, decide_eq_true_eq] using paid

theorem next_native (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    (next runtime frame (read runtime.tick.next.state)).native =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) := by
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [next, reindex_native]
  change cast (congrArg (SourceConditionalNativeObservers.State Key) (SourceActualImageStep.next_bound runtime).symm)
    (SourceConditionalNativeObservers.advance (fun _ => read runtime.tick.next.state) (inventoryBound runtime) frame.native) = _
  rw [source, receipt]
  have old : SourceConditionalNativeObservers.advance (fun _ => read (inventoryBound runtime + 1)) (inventoryBound runtime)
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime)) =
        SourceConditionalNativeObservers.generate read (inventoryBound runtime + 1) := rfl
  rw [old]
  have transport (left right : Nat) (same : left = right) :
      cast (congrArg (SourceConditionalNativeObservers.State Key) same) (SourceConditionalNativeObservers.generate read left) =
        SourceConditionalNativeObservers.generate read right := by
    cases same
    rfl
  exact transport _ _ (SourceActualImageStep.next_bound runtime).symm

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
