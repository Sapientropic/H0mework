import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.FreshRecoveryGain

/-!
# The original copy receiver consumes the new material recovery gain

The counted posterior reads the complete actual future-response fibre at d3.
The same generated stage carries the original whole ledger and canonical next,
while the original source-weighted G consumer records the strict gain over
the transported, erased old code.
-/

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordOriginalFreshRecovery

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceWordFutureBitGrowth SourceWordFreshRecoveryGain
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

theorem original_receiver_consumes_gain :
    let runtime := runtimeAt 3
    let word := SourceWordFreshReceiver.freshWord 3
    let actor : Actors runtime := ⟨0, by decide⟩
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    runtime = (runtimeAt 2).tick.next ∧
      SourcePosteriorReadback.readWeight runtime
        (SourceCountedPosterior.model runtime
          (SourceRetainedReceiver.trajectory_nonunit runtime
            SourceWordObservedCode.actual_nonunit 0)
          (SourceWordObservedCode.table runtime
            SourceWordObservedCode.actual_nonunit word 0)
          (SourceWordObservedCode.sourceQuery runtime word actor)) =
        SourceConditionalHistory.conditional
          (historyPMF (inventoryBound runtime))
          (SourceWordFutureBit.futureRead runtime word)
          (SourceWordFutureBit.futureRead runtime word actor)
          (SourceWeightedRecovery.observed_supported _ _ actor
            (SourceUniformFibreVariance.source_positive _ actor)) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      0 < SourceConditionalInformationLoss.amount runtime freshRead forget ∧
      SourceWordCodeRisk.risk runtime word
        SourceWordFutureBitGrowth.carriedCode coarseDecoder =
        SourceWordCodeRisk.risk runtime word
          (SourceWordObservedCode.encodeObserved runtime word) fineDecoder +
        SourceWordFieldCode.gGap runtime word freshRead forget ∧
      SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word) fineDecoder <
      SourceWordCodeRisk.risk runtime word
        SourceWordFutureBitGrowth.carriedCode coarseDecoder ∧
      (1 / 2 : ℝ) ≤ SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word) fineDecoder ∧
      (3 / 4 : ℝ) ≤ SourceWordCodeRisk.risk runtime word
        SourceWordFutureBitGrowth.carriedCode coarseDecoder := by
  dsimp only
  exact ⟨(next_runtime 2).symm,
    SourceWordFutureBit.counted_future_posterior (runtimeAt 3)
      SourceWordObservedCode.actual_nonunit
      (SourceWordFreshReceiver.freshWord 3) (⟨0, by decide⟩ : Actors (runtimeAt 3)),
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 3)).factorizes.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt 3)).factorizes.2.2.2,
    info_pos, actual_gain,
    actual_gain_strict,
    SourceWordFreshReceiver.fresh_original_G_half_risk fineDecoder,
    SourceWordFutureBitGrowth.carriedCode_original_G_risk coarseDecoder⟩

end
end SourceWordOriginalFreshRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
