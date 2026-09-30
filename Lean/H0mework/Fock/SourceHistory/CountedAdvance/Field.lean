import H0mework.Fock.SourceHistory.CountedAdvance.Model
import H0mework.Fock.SourceHistory.CountedPosterior.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedAdvance

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open SourceRetainedReceiver (At)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem next_field_balance (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2)
    (depth : Nat) :
    let nextTable := SourceCountedObservation.step (inventoryBound runtime) table (clockRead 0 runtime.tick.next.state)
    SourceConditionalVector.dynamicError runtime.tick.next depth
      (SourceCountedObservation.observationTable runtime.tick.next nextTable depth) =
      SourceConditionalVector.dynamicVariance runtime.tick.next depth +
      ∑ actor : Actors runtime.tick.next, (historyPMF (inventoryBound runtime.tick.next) actor).toReal *
        ‖∑ key ∈ nextTable.keys.toFinset,
          (SourceCountedObservation.weight nextTable forgetClock (actor.val : ZMod 2) key : ℂ) •
            (SourceCountedObservation.readValue runtime.tick.next nextTable key -
              SourceConditionalVector.realizeModel runtime.tick.next
                (nextModel runtime nonunit table (clockRead 0 runtime.tick.next.state) key))‖ ^ 2 := by
  have nextKeys : (SourceRetainedReceiver.next runtime frame (clockRead 0 runtime.tick.next.state)).keys =
      SourceUniformFibreVariance.outputs (inventoryBound runtime.tick.next) (fun actor => clockRead 0 actor.val) := by
    rw [SourceRetainedCoarsening.next_keys, keys]
    exact SourceReceivedKeyInventory.keys_next runtime (clockRead 0)
  have nextSmall : ∀ key,
      ‖(((SourceRetainedReceiver.next runtime frame (clockRead 0 runtime.tick.next.state)).native key).1 : ℂ) •
        SourceRetainedReceiver.residual runtime.tick.next
          (SourceRetainedReceiver.next runtime frame (clockRead 0 runtime.tick.next.state)) key‖ < 1 / 2 := by
    intro key
    rw [SourceCountedPosterior.counted_residual_next runtime frame (clockRead 0) key native]
    exact margins key
  have paid := SourceCountedPosterior.field_balance runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
    (SourceCountedObservation.step (inventoryBound runtime) table (clockRead 0 runtime.tick.next.state))
    (SourceRetainedReceiver.next runtime frame (clockRead 0 runtime.tick.next.state))
    (SourceCountedRecovery.step_next_simulates runtime table frame source _)
    (SourceRetainedReceiver.next_native runtime frame (clockRead 0) native) nextKeys nextSmall depth
  simpa only [step_model_commutes runtime nonunit table frame (clockRead 0) _ source native margins] using paid

end
end SourceCountedAdvance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
