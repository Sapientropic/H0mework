import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.Search.Source.SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition

/-!
# Pointwise audit of UBI actionable-exit authority

The paid-replay authority coordinate is unpacked into its existing exact UBI
payment, settlement, feasible edge, actionable renewal, capacity and root
factorization.  Pointwise recognition audits this dependent authority; it does
not create or preauthorize it.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
open M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition

/-- The full dependent actionable-exit authority is injective on paid replay
occurrences. -/
theorem canonicalPaidReplay_actionableExitAuthority_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (fun replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex =>
        replay.2.authorityK) :=
  canonicalPaidReplay_authorityK_injective oldVisit sourceIndex

/-- Even the exact UBI payment occurrence projected from actionable-exit
authority remains injective on the paid replay source family. -/
theorem canonicalPaidReplay_actionableExitPayment_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (fun replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex =>
        replay.2.authorityK.paymentOccurrence) := by
  intro left right paymentEquality
  have currentEquality :
      contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex left.1 =
        contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex right.1 := by
    cases left with
    | mk leftDepth leftReplay =>
        cases right with
        | mk rightDepth rightReplay =>
            change
              (periodicActualServiceExitOccurrenceAt
                    (contributionCapacityPostSettlementFutureBirthCurrentAt
                      oldVisit sourceIndex leftDepth)).paymentOccurrence =
                (periodicActualServiceExitOccurrenceAt
                    (contributionCapacityPostSettlementFutureBirthCurrentAt
                      oldVisit sourceIndex rightDepth)).paymentOccurrence at paymentEquality
            rw [periodicActualServiceExit_paymentOccurrence,
              periodicActualServiceExit_paymentOccurrence] at paymentEquality
            exact periodicPaymentOccurrenceAt_injective paymentEquality
  unfold contributionCapacityPostSettlementFutureBirthCurrentAt at currentEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  apply canonicalPaidReplay_eq_of_depth_eq left right
  omega

/-- Pointwise audit of one recognized full actionable-exit authority. -/
theorem canonicalPaidReplayFairPointwiseActionableExitAudit
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    let search :=
      sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
        sourceIndex replay
    let recognized :=
      canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit
        sourceIndex replay
    let exitAuthority := replay.2.authorityK
    let depth := exitAuthority.2.depth
    let actualExit := exitAuthority.2.actualExit
    type_of%
        (canonicalPaidReplayFairTerminatingRecognition_directConsumer oldVisit
          sourceIndex replay) ∧
      recognized = replay ∧
      recognized.2.authorityK = exitAuthority ∧
      replay.2.futureBirth.actualExit = actualExit ∧
      exitAuthority.paymentOccurrence.1 = exitAuthority.1 ∧
      actualExit.paymentOccurrence = periodicSourceBackedPaymentAt depth ∧
      actualExit.paymentOccurrence.installed = installedUBIAt depth ∧
      actualExit.actualSettlement = actualSettlementAt depth ∧
      actualExit.feasibleEdge = firstFeasibleExitAt depth ∧
      actualExit.actionableRenewal = actionableExitRenewalAt depth ∧
      Nonempty
        ((geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt) ∧
      (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      type_of% actualExit.rootFactorization ∧
      type_of% (strongest_actual_exit_renewal_iff_at depth) ∧
      type_of% replay.2.paidStep_consumes_exactPayment ∧
      type_of% replay.2.paymentNext_isCanonicalTarget ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          search.stopStage) := by
  dsimp only
  let search :=
    sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
      sourceIndex replay
  let recognized :=
    canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit sourceIndex
      replay
  let exitAuthority := replay.2.authorityK
  let depth := exitAuthority.2.depth
  let actualExit := exitAuthority.2.actualExit
  have recognizedExact : recognized = replay :=
    canonicalPaidReplayFairTerminatingRecognizedOccurrence_exact oldVisit
      sourceIndex replay
  have recognizedAuthorityExact :
      recognized.2.authorityK = exitAuthority :=
    congrArg (fun paidReplay => paidReplay.2.authorityK) recognizedExact
  exact
    ⟨canonicalPaidReplayFairTerminatingRecognition_directConsumer oldVisit
        sourceIndex replay,
      recognizedExact,
      recognizedAuthorityExact,
      replay.2.actualAuthority_isFutureBirthActualExit,
      exitAuthority.paymentOccurrence_visit_eq,
      actualExit.paymentOccurrence_eq,
      actualExit.paymentInstalled_eq,
      actualExit.actualSettlement_eq,
      actualExit.feasibleEdge_eq,
      actualExit.actionableRenewal_eq,
      ⟨actualExit.actionableRenewal⟩,
      actualExit.exactCapacity,
      actualExit.capturedCapacity,
      actualExit.rootFactorization,
      strongest_actual_exit_renewal_iff_at depth,
      replay.2.paidStep_consumes_exactPayment,
      replay.2.paymentNext_isCanonicalTarget,
      canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
        search.stopStage⟩

end
end M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit.canonicalPaidReplay_actionableExitAuthority_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit.canonicalPaidReplay_actionableExitPayment_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit.canonicalPaidReplayFairPointwiseActionableExitAudit
