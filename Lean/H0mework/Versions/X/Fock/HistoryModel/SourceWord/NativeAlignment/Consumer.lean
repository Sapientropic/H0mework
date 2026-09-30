import H0mework.Versions.X.Fock.HistoryModel.SourceWord.NativeAlignment.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordNativeAlignment

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem next_model_same_as_original_coarse
    (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime)
      nonunit 0 * SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) (key : ZMod 2) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime)
      (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime)
        (fun actor => clockRead 0 actor.val)) samples
    let fineTable := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => clockRead 0 (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime)
        (maximumIndex runtime).val keys initial) steps
    SourceCountedAdvance.nextModel (runtime.advance steps)
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
        (SourceWordObservedCode.table runtime nonunit [] steps)
        (SourceWordObservedCode.readAt (inventoryBound runtime) []
          (runtime.advance steps).tick.next.state) key =
      SourceCountedAdvance.nextModel (runtime.advance steps)
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
        (SourceCountedMerge.mergeTable fineTable forgetClock)
        (forgetClock (clockRead 0 (runtime.advance steps).tick.next.state)) key := by
  dsimp only
  calc
    _ = SourceConditionalNativePosterior.model (runtime.advance steps).tick.next
        (SourceWordObservedCode.readAt (inventoryBound runtime) []) key :=
      SourceWordObservedCode.counted_next_model runtime nonunit [] steps key
    _ = SourceConditionalNativePosterior.model (runtime.advance steps).tick.next
        (forgetClock ∘ clockRead 0) key := by rw [native_read_fun]
    _ = _ := (SourceCountedMerge.continued_next_model runtime nonunit (clockRead 0)
      keys inventory samples budgets forgetClock steps key).symm

end
end SourceWordNativeAlignment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
