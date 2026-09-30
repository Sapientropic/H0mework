import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFreshReceiver

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem fresh_received (depth : Nat)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex (runtimeAt depth)).val ≠ 0)
    (steps : Nat) :
    SourceCountedObservation.Simulates
      (inventoryBound ((runtimeAt depth).advance steps))
      (SourceCopyCurrentCoordinates.maximumIndex ((runtimeAt depth).advance steps)).val
      (SourceWordObservedCode.table (runtimeAt depth) nonunit (freshWord depth) steps)
      (SourceRetainedReceiver.trajectory (runtimeAt depth)
        (SourceWordObservedCode.initial (runtimeAt depth) nonunit (freshWord depth))
        (fun offset => SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
          (freshWord depth) (inventoryBound (runtimeAt depth) + offset + 1)) steps) :=
  SourceWordObservedCode.received (runtimeAt depth) nonunit (freshWord depth) steps

theorem fresh_complete_posterior (depth : Nat)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex (runtimeAt depth)).val ≠ 0)
    (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound (runtimeAt depth))).map
      (fun actor : Actors (runtimeAt depth) =>
        SourceWordObservedCode.readAt depth [] actor.val *
          SourceWordObservedCode.observe
            ((runtimeAt depth).tick.next.current.visit.current : Current))).support) :
    SourcePosteriorReadback.readWeight (runtimeAt depth)
      (SourceCountedPosterior.model (runtimeAt depth)
        (SourceRetainedReceiver.trajectory_nonunit (runtimeAt depth) nonunit 0)
        (SourceWordObservedCode.table (runtimeAt depth) nonunit (freshWord depth) 0) key) =
      (fun actor => SourceConditionalHistory.conditional
        (historyPMF (inventoryBound (runtimeAt depth)))
        (fun index : Actors (runtimeAt depth) =>
          SourceWordObservedCode.readAt depth [] index.val *
            SourceWordObservedCode.observe
              ((runtimeAt depth).tick.next.current.visit.current : Current))
        key supported actor) := by
  have queryEq : SourceWordObservedCode.sourceQuery (runtimeAt depth) (freshWord depth) =
      (fun actor : Actors (runtimeAt depth) =>
        SourceWordObservedCode.readAt depth [] actor.val *
          SourceWordObservedCode.observe
            ((runtimeAt depth).tick.next.current.visit.current : Current)) := by
    funext actor
    exact fresh_query_all depth actor
  have supportedSource : key ∈ ((historyPMF (inventoryBound (runtimeAt depth))).map
      (SourceWordObservedCode.sourceQuery (runtimeAt depth) (freshWord depth))).support := by
    simpa only [queryEq] using supported
  simpa only [queryEq] using SourceWordObservedCode.counted_complete_posterior
    (runtimeAt depth) nonunit (freshWord depth) key supportedSource

theorem fresh_next_model (depth : Nat)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex (runtimeAt depth)).val ≠ 0)
    (steps : Nat) (key : ZMod 2) :
    SourceCountedAdvance.nextModel ((runtimeAt depth).advance steps)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt depth) nonunit steps)
      (SourceWordObservedCode.table (runtimeAt depth) nonunit (freshWord depth) steps)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth)) (freshWord depth)
        ((runtimeAt depth).advance steps).tick.next.state) key =
      SourceConditionalNativePosterior.model ((runtimeAt depth).advance steps).tick.next
        (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth)) (freshWord depth))
        key :=
  SourceWordObservedCode.counted_next_model
    (runtimeAt depth) nonunit (freshWord depth) steps key

theorem fresh_original_G_half_risk (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    (1 / 2 : ℝ) ≤ SourceWordCodeRisk.risk (runtimeAt 3) (freshWord 3)
      (SourceWordObservedCode.encodeObserved (runtimeAt 3) (freshWord 3)) decoder :=
  SourceWordObservedCode.actual_observed_half_risk (freshWord 3) decoder

theorem fresh_original_G_full_account (depth : Nat)
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    let runtime := runtimeAt depth
    let word := freshWord depth
    let query := fun actor : Actors runtime =>
      SourceWordObservedCode.readAt depth [] actor.val *
        SourceWordObservedCode.observe
          ((runtimeAt depth).tick.next.current.visit.current : Current)
    SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word) decoder =
      SourceConditionalInventory.cost (inventoryBound runtime) query /
        (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) query
          (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
            (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
              (inventoryBound runtime)))‖ ^ 2 +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceCompiledGWord.effect (inventoryBound runtime + 1) word
          (SourceVectorMoment.mean
            (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
              query (query actor)
              (SourceWeightedRecovery.observed_supported _ _ actor
                (SourceUniformFibreVariance.source_positive _ actor)))
            (SourceConditionalInventory.values (inventoryBound runtime))) -
          decoder (query actor)‖ ^ 2 := by
  dsimp only
  have queryEq : SourceWordCodeRisk.query (runtimeAt depth) (freshWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt depth) (freshWord depth)) =
      (fun actor : Actors (runtimeAt depth) =>
        SourceWordObservedCode.readAt depth [] actor.val *
          SourceWordObservedCode.observe
            ((runtimeAt depth).tick.next.current.visit.current : Current)) := by
    rw [SourceWordObservedCode.query_source]
    funext actor
    exact fresh_query_all depth actor
  simpa only [queryEq] using
    (SourceWordCodeRisk.risk_account (runtimeAt depth) (freshWord depth)
      (SourceWordObservedCode.encodeObserved (runtimeAt depth) (freshWord depth)) decoder)


end
end SourceWordFreshReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
