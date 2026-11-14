import H0mework.Versions.X.Fock.HistoryModel.Counted.Word
import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Information

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedWordTransport

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem native_word_counted_gap (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => SourceConditionalNativeObservers.clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => SourceConditionalNativeObservers.clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime)
        ((SourceCopyCurrentCoordinates.maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime
        (SourceCopyCurrentCoordinates.maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (SourceCopyCurrentCoordinates.maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (SourceCopyCurrentCoordinates.maximumIndex runtime) 0
          (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime
            (SourceCopyCurrentCoordinates.maximumIndex runtime) 0
            ((SourceCopyCurrentCoordinates.maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime
              (SourceConditionalNativeObservers.clockRead 0) key.val)) <
        SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime)
      (SourceCopyCurrentCoordinates.maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime)
        (fun actor => SourceConditionalNativeObservers.clockRead 0 actor.val)) samples
    let fineTable := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => SourceConditionalNativeObservers.clockRead 0 (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime)
        (SourceCopyCurrentCoordinates.maximumIndex runtime).val keys initial) steps
    let advanced := runtime.advance steps
    let current := advanced.tick.next
    let coarseTable := SourceCountedMerge.mergeTable fineTable SourceConditionalNativeMerge.forgetClock
    let nextCoarseTable := SourceCountedObservation.step (inventoryBound advanced) coarseTable
      (SourceConditionalNativeMerge.forgetClock
        (SourceConditionalNativeObservers.clockRead 0 advanced.tick.next.state))
    let read : Actors current → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound current + 1) :=
      fun index => SourceGeneratedActionWords.Fock.letterAction (inventoryBound current + 1) (.inl ())
        (SourceGeneratedActionWords.Fock.point (inventoryBound current + 1)
          ((runtimeAt index.val).current.visit.current : Current))
    let wordG : Actors current → SourceConditionalModel.NextModel current := fun actor =>
      ∑ candidate : Actors current,
        (((SourceConditionalHistory.conditional (historyPMF (inventoryBound current)) read (read actor)
          (SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound current)) read actor
            (SourceConditionalModel.positive current actor))) candidate).toReal : ℂ) •
          nextRead current candidate
    (∑ actor : Actors current,
      ((((SourceGeneratedActionWords.Fock.sourceLaw (inventoryBound current)).map nativeStep).map
        (SourceGeneratedActionWords.Fock.point (inventoryBound current + 1))) (read actor)).toReal *
      ‖SourceConditionalVector.realizeModel current (wordG actor) -
        SourceConditionalVector.realizeModel current
          (SourceCountedPosterior.model current (SourceMinimumSharedNext.next_nonunit advanced)
            nextCoarseTable (SourceConditionalNativeMerge.forgetClock
              (SourceConditionalNativeObservers.clockRead 0 actor.val)))‖ ^ 2) =
      SourceConditionalMergeLoss.gap current (SourceConditionalNativeObservers.clockRead 0)
        SourceConditionalNativeMerge.forgetClock := by
  dsimp only
  rw [← SourceCountedMerge.continued_next_table_loss runtime nonunit keys inventory samples budgets steps]
  apply Finset.sum_congr rfl
  intro actor _
  have recovered := native_word_g_recovers (runtime.advance steps).tick.next actor
  rw [native_word_mass (runtime.advance steps).tick.next actor, recovered]

theorem native_word_counted_strict (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => SourceConditionalNativeObservers.clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => SourceConditionalNativeObservers.clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime)
        ((SourceCopyCurrentCoordinates.maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime
        (SourceCopyCurrentCoordinates.maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (SourceCopyCurrentCoordinates.maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (SourceCopyCurrentCoordinates.maximumIndex runtime) 0
          (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime
            (SourceCopyCurrentCoordinates.maximumIndex runtime) 0
            ((SourceCopyCurrentCoordinates.maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime
              (SourceConditionalNativeObservers.clockRead 0) key.val)) <
        SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime)
      (SourceCopyCurrentCoordinates.maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime)
        (fun actor => SourceConditionalNativeObservers.clockRead 0 actor.val)) samples
    let fineTable := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => SourceConditionalNativeObservers.clockRead 0 (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime)
        (SourceCopyCurrentCoordinates.maximumIndex runtime).val keys initial) steps
    let advanced := runtime.advance steps
    let current := advanced.tick.next
    let coarseTable := SourceCountedMerge.mergeTable fineTable SourceConditionalNativeMerge.forgetClock
    let nextCoarseTable := SourceCountedObservation.step (inventoryBound advanced) coarseTable
      (SourceConditionalNativeMerge.forgetClock
        (SourceConditionalNativeObservers.clockRead 0 advanced.tick.next.state))
    let read : Actors current → SourceGeneratedActionWords.Fock.WholeModel (inventoryBound current + 1) :=
      fun index => SourceGeneratedActionWords.Fock.letterAction (inventoryBound current + 1) (.inl ())
        (SourceGeneratedActionWords.Fock.point (inventoryBound current + 1)
          ((runtimeAt index.val).current.visit.current : Current))
    let wordG : Actors current → SourceConditionalModel.NextModel current := fun actor =>
      ∑ candidate : Actors current,
        (((SourceConditionalHistory.conditional (historyPMF (inventoryBound current)) read (read actor)
          (SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound current)) read actor
            (SourceConditionalModel.positive current actor))) candidate).toReal : ℂ) •
          nextRead current candidate
    0 < (∑ actor : Actors current,
      ((((SourceGeneratedActionWords.Fock.sourceLaw (inventoryBound current)).map nativeStep).map
        (SourceGeneratedActionWords.Fock.point (inventoryBound current + 1))) (read actor)).toReal *
      ‖SourceConditionalVector.realizeModel current (wordG actor) -
        SourceConditionalVector.realizeModel current
          (SourceCountedPosterior.model current (SourceMinimumSharedNext.next_nonunit advanced)
            nextCoarseTable (SourceConditionalNativeMerge.forgetClock
              (SourceConditionalNativeObservers.clockRead 0 actor.val)))‖ ^ 2) ∧
      0 < SourceConditionalInformationLoss.amount current
        (SourceConditionalNativeObservers.clockRead 0) SourceConditionalNativeMerge.forgetClock := by
  dsimp only
  have equation := native_word_counted_gap runtime nonunit keys inventory samples budgets steps
  have paid := SourceCountedMerge.continued_next_table_strict runtime nonunit keys inventory samples budgets steps
  dsimp only at equation paid
  refine ⟨?_, paid.2⟩
  rw [equation]
  exact (SourceConditionalInformationLoss.amount_positive_iff_gap
    (runtime.advance steps).tick.next (SourceConditionalNativeObservers.clockRead 0)
      SourceConditionalNativeMerge.forgetClock).mp paid.2

end
end SourceCountedWordTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
