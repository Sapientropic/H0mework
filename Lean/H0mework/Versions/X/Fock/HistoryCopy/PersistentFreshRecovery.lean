import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.PersistentRecoveryGain

/-!
# Original Copy receiver consumes the persistent material gain

At every exact successor, the original counted posterior reads every actor's
complete future-response conditional. The same stage retains the source
ledger, literal next, positive information difference, and strict G gain.
-/

set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordPersistentCopyRecovery

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

open SourceWordPersistentMaterial SourceWordPersistentRecoveryGain

noncomputable section

theorem original_receiver_consumes_persistent_gain (offset : Nat) :
    let runtime := runtimeAt (depth offset)
    let word := freshWord offset
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    runtime = (runtimeAt 3).advance offset ∧
      (∀ actor : Actors runtime,
        SourcePosteriorReadback.readWeight runtime
          (SourceCountedPosterior.model runtime
            (SourceRetainedReceiver.trajectory_nonunit runtime
              (nonunitAt offset) 0)
            (SourceWordObservedCode.table runtime
              (nonunitAt offset) word 0)
            (SourceWordObservedCode.sourceQuery runtime word actor)) =
          SourceConditionalHistory.conditional
            (historyPMF (inventoryBound runtime))
            (SourceWordFutureBit.futureRead runtime word)
            (SourceWordFutureBit.futureRead runtime word actor)
            (SourceWeightedRecovery.observed_supported _ _ actor
              (SourceUniformFibreVariance.source_positive _ actor))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      0 < SourceConditionalInformationLoss.amount runtime (fineRead offset) forget ∧
      SourceWordCodeRisk.risk runtime word (oldCode offset)
          (coarseDecoder offset) =
        SourceWordCodeRisk.risk runtime word
          (SourceWordObservedCode.encodeObserved runtime word)
          (fineDecoder offset) +
        SourceWordFieldCode.gGap runtime word (fineRead offset) forget ∧
      SourceWordCodeRisk.risk runtime word
          (SourceWordObservedCode.encodeObserved runtime word)
          (fineDecoder offset) <
        SourceWordCodeRisk.risk runtime word (oldCode offset)
          (coarseDecoder offset) := by
  dsimp only
  exact ⟨runtime_from_original offset,
    (fun actor => SourceWordFutureBit.counted_future_posterior
      (runtimeAt (depth offset)) (nonunitAt offset)
      (freshWord offset) actor),
    (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtimeAt (depth offset))).factorizes.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtimeAt (depth offset))).factorizes.2.2.2,
    info_pos offset, actual_gain offset, actual_gain_strict offset⟩


end
end SourceWordPersistentCopyRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
