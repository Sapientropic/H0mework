import H0mework.Versions.X.Fock.SourceHistory.CountedAdvance.State

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedAdvance

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors NextModel nextRead)
open SourceRetainedReceiver (At)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def nextModel (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (added key : Key) : NextModel runtime.tick.next :=
  SourceFibreExactState.nextModel runtime nonunit
    (samples (inventoryBound runtime) (maximumIndex runtime).val table) added key

theorem next_model_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2) :
    nextModel runtime nonunit table (read runtime.tick.next.state) key =
      SourceConditionalNativePosterior.model runtime.tick.next read key := by
  have aligned (left right : Nat) (same : left = right) (actor : Fin (left + 1)) :
      (SourceConditionalNativeObservers.generate read right key).2 (Fin.cast (congrArg Nat.succ same) actor) =
        (SourceConditionalNativeObservers.generate read left key).2 actor := by
    cases same
    rfl
  have generated : SourceFibreExactState.next (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (samples (inventoryBound runtime) (maximumIndex runtime).val table) (read runtime.tick.next.state) =
        SourceConditionalNativeObservers.generate read (inventoryBound runtime + 1) :=
    next_source runtime nonunit table frame read source native margins
  rw [nextModel, SourceFibreExactState.nextModel, generated, SourceConditionalNativePosterior.model]
  apply Finset.sum_congr rfl
  intro actor _
  rw [aligned _ _ (SourceActualImageStep.next_bound runtime) actor]

theorem step_model_commutes (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2) :
    SourceCountedPosterior.model runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
      (SourceCountedObservation.step (inventoryBound runtime) table (read runtime.tick.next.state)) key =
        nextModel runtime nonunit table (read runtime.tick.next.state) key := by
  have nextSmall :
      ‖(((SourceRetainedReceiver.next runtime frame (read runtime.tick.next.state)).native key).1 : ℂ) •
        SourceRetainedReceiver.residual runtime.tick.next
          (SourceRetainedReceiver.next runtime frame (read runtime.tick.next.state)) key‖ < 1 / 2 := by
    rw [SourceCountedPosterior.counted_residual_next runtime frame read key native]
    exact margins key
  have recovered := SourceCountedPosterior.model_source runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
    (SourceCountedObservation.step (inventoryBound runtime) table (read runtime.tick.next.state))
    (SourceRetainedReceiver.next runtime frame (read runtime.tick.next.state)) read key
    (SourceCountedRecovery.step_next_simulates runtime table frame source _)
    (SourceRetainedReceiver.next_native runtime frame read native) nextSmall
  exact recovered.trans (next_model_source runtime nonunit table frame read key source native margins).symm

end
end SourceCountedAdvance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
