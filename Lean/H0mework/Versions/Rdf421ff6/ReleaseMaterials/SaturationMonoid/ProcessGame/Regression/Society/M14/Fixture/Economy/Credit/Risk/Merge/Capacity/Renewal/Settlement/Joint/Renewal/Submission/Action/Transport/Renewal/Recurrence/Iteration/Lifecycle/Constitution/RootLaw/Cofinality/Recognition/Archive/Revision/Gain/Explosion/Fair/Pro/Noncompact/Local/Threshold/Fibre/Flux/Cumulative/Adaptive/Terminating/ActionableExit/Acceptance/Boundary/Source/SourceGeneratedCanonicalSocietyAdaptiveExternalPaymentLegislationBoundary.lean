import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Root.Universal.Observer.ProofCarryingUniversalObserverConsumerExhaustionRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Consumer.ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Policy.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Audit.Source.SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Seal.Source.SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal

/-!
# Adaptive two-target external-Payment legislation boundary

One finite adaptive Payment proposal is forced onto two adjacent source spans.
Their exact Payment/PCL indices differ, so joint source acceptance is empty,
while each canonical source target is individually accepted and produces the
next paid self-U8 span.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14ProofCarryingUniversalObserverConsumerExhaustionRegression
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy.CanonicalPaidReplayFairFiniteAdaptivePolicy
open M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal

/-- The source submission of a span is literally the actual universal grammar
occurrence at the same boundary. -/
theorem externalPaymentSpan_sourceSubmission_isActualGrammar
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    (sourceSubmission span).exactEvent =
      (universalSocietyActualGrammarAt oldVisit sourceIndex boundary
        ).exactEvent := by
  cases span
  rfl

/-- Adjacent source spans carry distinct heterogeneous Payment occurrences. -/
theorem adjacentExternalPaymentSpan_targets_ne
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let leftSpan :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary
    let rightSpan :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex (boundary + 1)
    targetAnyPaymentOccurrence leftSpan ≠
      targetAnyPaymentOccurrence rightSpan := by
  dsimp only
  let leftSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  let rightSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + 1)
  intro paymentEquality
  have replayEquality :=
    canonicalPaidReplay_actionableExitPayment_injective oldVisit sourceIndex
      paymentEquality
  have depthEquality := congrArg Sigma.fst replayEquality
  change boundary + 2 = boundary + 1 + 2 at depthEquality
  omega

/-- Maximum source-native acceptance boundary for one finite adaptive Payment
proposal. -/
theorem finiteAdaptivePaymentProposal_generatesExactLegislationBoundary
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat) {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy
      AnySourceBackedPaymentOccurrence fuel) :
    let cutoff := adaptivePolicyCutoff requestedStage policy
    let leftSpan :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex cutoff
    let rightSpan :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex (cutoff + 1)
    let leftReplay := rightReplayAt oldVisit sourceIndex cutoff
    let rightReplay := rightReplayAt oldVisit sourceIndex (cutoff + 1)
    let recurrence :=
      canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex cutoff
    policy.run leftReplay = policy.run rightReplay ∧
      targetAnyPaymentOccurrence leftSpan ≠
        targetAnyPaymentOccurrence rightSpan ∧
      IsEmpty
        (SourceAcceptedExternalPaymentLegislationAt leftSpan
              (policy.run leftReplay) (targetLegislation leftSpan) ×
          SourceAcceptedExternalPaymentLegislationAt rightSpan
            (policy.run rightReplay) (targetLegislation rightSpan)) ∧
      Nonempty
        (SourceAcceptedExternalPaymentLegislationAt leftSpan
          (targetAnyPaymentOccurrence leftSpan)
          (targetLegislation leftSpan)) ∧
      Nonempty
        (SourceAcceptedExternalPaymentLegislationAt rightSpan
          (targetAnyPaymentOccurrence rightSpan)
          (targetLegislation rightSpan)) ∧
      type_of%
        (proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
          leftSpan) ∧
      type_of%
        (proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
          rightSpan) ∧
      type_of%
        (universalSocietySearchTypedRejection oldVisit sourceIndex cutoff) ∧
      type_of%
        (universalSocietySearchTypedRejection oldVisit sourceIndex
          (cutoff + 1)) ∧
      (sourceSubmission leftSpan).exactEvent =
        (universalSocietyActualGrammarAt oldVisit sourceIndex cutoff
          ).exactEvent ∧
      (sourceSubmission rightSpan).exactEvent =
        (universalSocietyActualGrammarAt oldVisit sourceIndex (cutoff + 1)
          ).exactEvent ∧
      type_of% leftSpan.sourceTargetOccurrencesDistinct ∧
      type_of% rightSpan.sourceTargetOccurrencesDistinct ∧
      type_of% leftSpan.targetLegislationOccurrence_isPaymentOccurrence ∧
      type_of% rightSpan.targetLegislationOccurrence_isPaymentOccurrence ∧
      type_of% recurrence.2.2 ∧
      nextSpan recurrence.2.1 = rightSpan := by
  dsimp only
  let cutoff := adaptivePolicyCutoff requestedStage policy
  let leftSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex cutoff
  let rightSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (cutoff + 1)
  let leftReplay := rightReplayAt oldVisit sourceIndex cutoff
  let rightReplay := rightReplayAt oldVisit sourceIndex (cutoff + 1)
  let recurrence :=
    canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
      oldVisit sourceIndex cutoff
  have boundLtCutoff : zeroBranchBound policy < cutoff :=
    zeroBranchBound_lt_adaptivePolicyCutoff requestedStage policy
  have leftRun : policy.run leftReplay = policy.zeroBranchAnswer :=
    policy.run_eq_zeroBranchAnswer_of_bound_lt leftReplay (by
      change zeroBranchBound policy < cutoff + 2
      omega)
  have rightRun : policy.run rightReplay = policy.zeroBranchAnswer :=
    policy.run_eq_zeroBranchAnswer_of_bound_lt rightReplay (by
      change zeroBranchBound policy < cutoff + 1 + 2
      omega)
  have outputEquality : policy.run leftReplay = policy.run rightReplay :=
    leftRun.trans rightRun.symm
  have targetPaymentsNe :
      targetAnyPaymentOccurrence leftSpan ≠
        targetAnyPaymentOccurrence rightSpan :=
    adjacentExternalPaymentSpan_targets_ne oldVisit sourceIndex cutoff
  have jointAcceptanceEmpty :
      IsEmpty
        (SourceAcceptedExternalPaymentLegislationAt leftSpan
              (policy.run leftReplay) (targetLegislation leftSpan) ×
          SourceAcceptedExternalPaymentLegislationAt rightSpan
            (policy.run rightReplay) (targetLegislation rightSpan)) :=
    ⟨fun acceptances => by
      have leftExact := acceptances.1.proposalExact
      have rightExact := acceptances.2.proposalExact
      apply targetPaymentsNe
      exact leftExact.symm.trans (outputEquality.trans rightExact)⟩
  exact
    ⟨outputEquality,
      targetPaymentsNe,
      jointAcceptanceEmpty,
      ⟨sourceAcceptedExternalPaymentLegislationAt leftSpan⟩,
      ⟨sourceAcceptedExternalPaymentLegislationAt rightSpan⟩,
      proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
        leftSpan,
      proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
        rightSpan,
      universalSocietySearchTypedRejection oldVisit sourceIndex cutoff,
      universalSocietySearchTypedRejection oldVisit sourceIndex (cutoff + 1),
      externalPaymentSpan_sourceSubmission_isActualGrammar leftSpan,
      externalPaymentSpan_sourceSubmission_isActualGrammar rightSpan,
      leftSpan.sourceTargetOccurrencesDistinct,
      rightSpan.sourceTargetOccurrencesDistinct,
      leftSpan.targetLegislationOccurrence_isPaymentOccurrence,
      rightSpan.targetLegislationOccurrence_isPaymentOccurrence,
      recurrence.2.2,
      rfl⟩

end
end M14SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary.externalPaymentSpan_sourceSubmission_isActualGrammar
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary.adjacentExternalPaymentSpan_targets_ne
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary.finiteAdaptivePaymentProposal_generatesExactLegislationBoundary
