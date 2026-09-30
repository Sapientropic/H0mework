import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Continuation
import H0mework.Versions.X.Fock.SourceHistory.CountedRecovery.Table

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedAdvance

variable {Key : Type*} [DecidableEq Key]

def samples (bound stride : Nat) (table : SourceCountedObservation.Table Key) (key : Key) :
    SourceRationalWindowReadout.Samples bound (stride + 1) :=
  let entry := SourceCountedObservation.lookup table key
  SourceReceivedConditionalStep.completeSamples bound stride
    ((fun position => SourceCountedObservation.coordinate entry.hilbert position.val / (bound + 1 : Nat)),
      entry.mass / (bound + 1 : Nat), entry.clock / (bound + 1 : Nat))

def next (bound stride : Nat) (nonunit : stride ≠ 0)
    (table : SourceCountedObservation.Table Key) (added : Key) : SourceConditionalNativeObservers.State Key (bound + 1) :=
  SourceFibreExactState.next bound stride nonunit (samples bound stride table) added

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceRetainedReceiver (At)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem next_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2) :
    next (inventoryBound runtime) (maximumIndex runtime).val nonunit table (read runtime.tick.next.state) =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime + 1) := by
  have restored : SourceFibreExactState.restoreState (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (samples (inventoryBound runtime) (maximumIndex runtime).val table) =
        SourceConditionalNativeObservers.generate read (inventoryBound runtime) := by
    funext key
    exact SourceCountedPosterior.restored_source runtime nonunit table frame read key source native (margins key)
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [next, SourceFibreExactState.next, restored, receipt, SourceConditionalNativeObservers.generated_next]
  rfl

theorem step_commutes (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2) :
    cast (congrArg (SourceConditionalNativeObservers.State Key) (SourceActualImageStep.next_bound runtime))
      (fun key => SourceCountedPosterior.restore (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
        (SourceMinimumSharedNext.next_nonunit runtime)
        (SourceCountedObservation.step (inventoryBound runtime) table (read runtime.tick.next.state)) key) =
      next (inventoryBound runtime) (maximumIndex runtime).val nonunit table (read runtime.tick.next.state) := by
  have restored :
      (fun key => SourceCountedPosterior.restore (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
        (SourceMinimumSharedNext.next_nonunit runtime)
        (SourceCountedObservation.step (inventoryBound runtime) table (read runtime.tick.next.state)) key) =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) := by
    funext key
    apply SourceCountedPosterior.restored_source runtime.tick.next _ _
      (SourceRetainedReceiver.next runtime frame (read runtime.tick.next.state)) read key
      (SourceCountedRecovery.step_next_simulates runtime table frame source _)
      (SourceRetainedReceiver.next_native runtime frame read native)
    rw [SourceCountedPosterior.counted_residual_next runtime frame read key native]
    exact margins key
  have transport (left right : Nat) (same : left = right) :
      cast (congrArg (SourceConditionalNativeObservers.State Key) same)
        (SourceConditionalNativeObservers.generate read left) = SourceConditionalNativeObservers.generate read right := by
    cases same
    rfl
  rw [restored, transport _ _ (SourceActualImageStep.next_bound runtime),
    next_source runtime nonunit table frame read source native margins]

end
end SourceCountedAdvance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
