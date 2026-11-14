import H0mework.Versions.R453de275.Fock.HistoryCopy.Consumer
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.ObservedCode.Future.Growth.Receiver.OddBirthOptimal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordOddBirth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- The actual odd-to-even material birth erases the new bit but retains the
old transported G task. The original Copy receiver charges that erasure at the
same generated row and next, with both complete future-response posteriors. -/
theorem original_copy_consumes_odd_erasure (depth : Nat) (odd : Odd depth) :
    let runtime := runtimeAt (depth + 1)
    let oldWord := SourceWordEvenBirth.oldWord depth
    let newWord := SourceWordEvenBirth.newWord depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    SourceCopyObservation.CurrentAt runtime ∧
      runtime = (runtimeAt depth).tick.next ∧
      ((runtimeAt depth).tick.next.current.visit.current : Current) ≠
        ((runtimeAt (depth + 1)).tick.next.current.visit.current : Current) ∧
      (∀ actor : Actors runtime,
        SourceWordObservedCode.sourceQuery runtime oldWord actor =
          SourceWordObservedCode.readAt depth [] actor.val ∧
        SourceWordObservedCode.sourceQuery runtime newWord actor = 0 ∧
        SourcePosteriorReadback.readWeight runtime
          (SourceCountedPosterior.model runtime
            (SourceRetainedReceiver.trajectory_nonunit runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) 0)
            (SourceWordObservedCode.table runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) oldWord 0)
            (SourceWordObservedCode.sourceQuery runtime oldWord actor)) =
          SourceConditionalHistory.conditional
            (historyPMF (inventoryBound runtime))
            (SourceWordFutureBit.futureRead runtime oldWord)
            (SourceWordFutureBit.futureRead runtime oldWord actor)
            (SourceWeightedRecovery.observed_supported _ _ actor
              (SourceUniformFibreVariance.source_positive _ actor)) ∧
        SourcePosteriorReadback.readWeight runtime
          (SourceCountedPosterior.model runtime
            (SourceRetainedReceiver.trajectory_nonunit runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) 0)
            (SourceWordObservedCode.table runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) newWord 0)
            (SourceWordObservedCode.sourceQuery runtime newWord actor)) =
          SourceConditionalHistory.conditional
            (historyPMF (inventoryBound runtime))
            (SourceWordFutureBit.futureRead runtime newWord)
            (SourceWordFutureBit.futureRead runtime newWord actor)
            (SourceWeightedRecovery.observed_supported _ _ actor
              (SourceUniformFibreVariance.source_positive _ actor))) ∧
      (∀ decode : SourceWordEvenBirth.FutureResponse depth →
          SourceWordEvenBirth.FutureResponse depth,
        ¬ ∀ actor : Actors runtime,
          decode (SourceWordFutureBit.futureRead runtime newWord actor) =
            SourceWordFutureBit.futureRead runtime oldWord actor) ∧
      0 < SourceConditionalInformationLoss.amount runtime (fineRead depth) forget ∧
      0 < SourceWordFieldCode.gGap runtime oldWord (fineRead depth) forget ∧
      SourceWordCodeRisk.risk runtime oldWord (freshCode depth) (freshBest depth) =
        SourceWordCodeRisk.risk runtime oldWord
          (SourceWordObservedCode.encodeObserved runtime oldWord) (oldBest depth) +
        SourceWordFieldCode.gGap runtime oldWord (fineRead depth) forget ∧
      SourceWordCodeRisk.risk runtime oldWord
          (SourceWordObservedCode.encodeObserved runtime oldWord) (oldBest depth) <
        SourceWordCodeRisk.risk runtime oldWord (freshCode depth) (freshBest depth) ∧
      type_of% (SourceWordCodeRisk.risk_account runtime oldWord
        (freshCode depth) (freshBest depth)) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent := by
  dsimp only
  let runtime := runtimeAt (depth + 1)
  let oldWord := SourceWordEvenBirth.oldWord depth
  let newWord := SourceWordEvenBirth.newWord depth
  exact ⟨SourceCopyObservation.current_consumed runtime,
    (SourceWordFutureBitGrowth.next_runtime depth).symm,
    SourceWordEvenBirth.old_new_material_distinct depth,
    (fun actor => ⟨old_query_native depth odd actor,
      new_query_zero depth odd actor,
      SourceWordFutureBit.counted_future_posterior runtime
        (SourceWordFutureBitGrowth.nextNonunit depth) oldWord actor,
      SourceWordFutureBit.counted_future_posterior runtime
        (SourceWordFutureBitGrowth.nextNonunit depth) newWord actor⟩),
    fresh_future_cannot_recover_old depth odd,
    information_loss_pos depth odd, gain_pos depth odd,
    exact_erasure_gain depth odd, strict_erasure_gain depth odd,
    SourceWordCodeRisk.risk_account runtime oldWord (freshCode depth)
      (freshBest depth),
    (SourceGeneratedRuntimeMaterialStageAt.generate runtime).factorizes.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate runtime).factorizes.2.2.2⟩

end
end SourceWordOddBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
