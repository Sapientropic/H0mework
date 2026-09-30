import H0mework.Fock.SourceHistory.CountedObservation.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

variable {Key : Type*} [DecidableEq Key]
noncomputable section

theorem value_lookup (runtime : LivingRuntimeState process) (table : Table Key)
    (frame : At runtime Key) (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (receipts : Nat → Key) (steps : Nat) (key : Key)
    (positive : ((SourceRetainedReceiver.run (inventoryBound runtime) (maximumIndex runtime).val
      receipts frame steps).native key).1 ≠ 0) :
    SourceRetainedReceiver.value (runtime.advance steps)
      (SourceRetainedReceiver.trajectory runtime frame receipts steps) key =
      SourceReceivedConditionalStep.completeValue (runtime.advance steps)
        (maximumIndex (runtime.advance steps)) 0
        (cast (congrArg₂ Raw
          (SourceGraphRecurrence.advance_depth runtime steps).symm
          (SourceRetainedReceiver.maximum_advance runtime steps).symm)
          (decode (inventoryBound runtime + steps) ((maximumIndex runtime).val + steps)
            (lookup (run (inventoryBound runtime) receipts table steps) key))) := by
  rw [SourceRetainedReceiver.value, SourceRetainedReceiver.trajectory,
    SourceRetainedReceiver.reindex_raw]
  have raw := observed_raw (inventoryBound runtime) (maximumIndex runtime).val table frame
    source receipts steps key positive
  rw [raw]

theorem residual_lookup (runtime : LivingRuntimeState process) (table : Table Key)
    (frame : At runtime Key) (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (receipts : Nat → Key) (steps : Nat) (key : Key)
    (positive : ((SourceRetainedReceiver.run (inventoryBound runtime) (maximumIndex runtime).val
      receipts frame steps).native key).1 ≠ 0) :
    (SourceReceivedConditionalStep.completeValue (runtime.advance steps)
      (maximumIndex (runtime.advance steps)) 0
      (cast (congrArg₂ Raw
        (SourceGraphRecurrence.advance_depth runtime steps).symm
        (SourceRetainedReceiver.maximum_advance runtime steps).symm)
        (decode (inventoryBound runtime + steps) ((maximumIndex runtime).val + steps)
          (lookup (run (inventoryBound runtime) receipts table steps) key))) -
      SourceConditionalVector.realizeModel (runtime.advance steps)
        (SourceRetainedReceiver.model (runtime.advance steps)
          (SourceRetainedReceiver.trajectory runtime frame receipts steps) key)) =
      SourceRetainedReceiver.residual (runtime.advance steps)
        (SourceRetainedReceiver.trajectory runtime frame receipts steps) key := by
  rw [SourceRetainedReceiver.residual]
  rw [value_lookup runtime table frame source receipts steps key positive]

theorem residual_energy_lookup (runtime : LivingRuntimeState process) (table : Table Key)
    (frame : At runtime Key) (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (receipts : Nat → Key) (steps : Nat) (key : Key)
    (positive : ((SourceRetainedReceiver.run (inventoryBound runtime) (maximumIndex runtime).val
      receipts frame steps).native key).1 ≠ 0) :
    ‖(SourceReceivedConditionalStep.completeValue (runtime.advance steps)
      (maximumIndex (runtime.advance steps)) 0
      (cast (congrArg₂ Raw
        (SourceGraphRecurrence.advance_depth runtime steps).symm
        (SourceRetainedReceiver.maximum_advance runtime steps).symm)
        (decode (inventoryBound runtime + steps) ((maximumIndex runtime).val + steps)
          (lookup (run (inventoryBound runtime) receipts table steps) key))) -
      SourceConditionalVector.realizeModel (runtime.advance steps)
        (SourceRetainedReceiver.model (runtime.advance steps)
          (SourceRetainedReceiver.trajectory runtime frame receipts steps) key))‖ ^ 2 =
      ‖SourceRetainedReceiver.residual (runtime.advance steps)
        (SourceRetainedReceiver.trajectory runtime frame receipts steps) key‖ ^ 2 := by
  rw [residual_lookup runtime table frame source receipts steps key positive]

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
