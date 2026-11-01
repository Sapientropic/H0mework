import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Effect.Consumer.ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEffect

/-!
# Proof-carrying accepted legislation enactment recurrence

The exact accepted effect generates a fresh proposal, acceptance and accepted
consumer through one actual paid-self-U8 recurrence step.  No future table or
second runtime is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14ProofCarryingUniversalObserverConsumerExhaustionRegression
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance
open M14ProofCarryingCanonicalSocietyCofinalExternalPaymentLegislationAntichain
open M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEffect

theorem acceptedProposal_ne_nextPointwiseProposal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation :
      TargetLegislationAt
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)
        proposal legislation) :
    proposal ≠
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + 1) := by
  intro proposalEquality
  let current :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  let next :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + 1)
  have currentExact : proposal = targetAnyPaymentOccurrence current :=
    acceptance.proposalExact
  have nextExact :
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + 1) =
        targetAnyPaymentOccurrence next :=
    pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
      (boundary + 1) next
  have boundaryEquality : boundary = boundary + 1 :=
    externalPaymentLegislationTarget_injective oldVisit sourceIndex
      (currentExact.symm.trans (proposalEquality.trans nextExact))
  omega

structure AcceptedExternalPaymentLegislationEnactmentRecurrenceFactsAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation :
      TargetLegislationAt
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)
        proposal legislation) : Prop where
  currentEffect : AcceptedExternalPaymentLegislationEffectFactsAt acceptance
  nextSpanExact :
    let recurrence :=
      canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex boundary
    nextSpan recurrence.2.1 =
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex (boundary + 1)
  paidTargetIsNextSourceEvent :
    type_of%
      (canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex boundary).2.2.paidTargetIsNextSourceEvent
  paidTargetIsNextSpanPayment :
    type_of%
      (canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex boundary).2.2.paidTargetIsNextSpanPayment
  proposalFresh :
    type_of% (acceptedProposal_ne_nextPointwiseProposal acceptance)
  nextAcceptance :
    let recurrence :=
      canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex boundary
    Nonempty
      (SourceAcceptedExternalPaymentLegislationAt
        (nextSpan recurrence.2.1)
        (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + 1))
        (targetLegislation (nextSpan recurrence.2.1)))
  nextAcceptedConsumerExact :
    let recurrence :=
      canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex boundary
    HEq
      (pointwiseAcceptanceAt oldVisit sourceIndex
        (boundary + 1)).independentConsumer
      (targetConsumer (nextSpan recurrence.2.1))
  nextWholeLedgerWriteBack :
    Nonempty
      (type_of%
        (pointwiseAcceptanceAt oldVisit sourceIndex
          (boundary + 1)).independentConsumer.wholeLedgerWriteBack)
  nextRevolutionaryBranch :
    type_of%
      (pointwiseAcceptanceAt oldVisit sourceIndex
        (boundary + 1)).independentConsumer_branchKind_isRevolution
  currentSearchTypedRejection :
    type_of%
      (universalSocietySearchTypedRejection oldVisit sourceIndex boundary)
  nextSearchTypedRejection :
    type_of%
      (universalSocietySearchTypedRejection oldVisit sourceIndex
        (boundary + 1))

theorem sourceAcceptedExternalPaymentLegislation_enactsAndGeneratesFreshNext
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation :
      TargetLegislationAt
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)
        proposal legislation) :
    AcceptedExternalPaymentLegislationEnactmentRecurrenceFactsAt acceptance where
  currentEffect :=
    sourceAcceptedExternalPaymentLegislation_enactsExactEffect acceptance
  nextSpanExact := rfl
  paidTargetIsNextSourceEvent :=
    (canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
      oldVisit sourceIndex boundary).2.2.paidTargetIsNextSourceEvent
  paidTargetIsNextSpanPayment :=
    (canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
      oldVisit sourceIndex boundary).2.2.paidTargetIsNextSpanPayment
  proposalFresh := acceptedProposal_ne_nextPointwiseProposal acceptance
  nextAcceptance :=
    ⟨pointwiseAcceptanceAt oldVisit sourceIndex (boundary + 1)⟩
  nextAcceptedConsumerExact :=
    (pointwiseAcceptanceAt oldVisit sourceIndex
      (boundary + 1)).independentConsumer_heq_targetConsumer
  nextWholeLedgerWriteBack :=
    ⟨(pointwiseAcceptanceAt oldVisit sourceIndex
      (boundary + 1)).independentConsumer.wholeLedgerWriteBack⟩
  nextRevolutionaryBranch :=
    (pointwiseAcceptanceAt oldVisit sourceIndex
      (boundary + 1)).independentConsumer_branchKind_isRevolution
  currentSearchTypedRejection :=
    universalSocietySearchTypedRejection oldVisit sourceIndex boundary
  nextSearchTypedRejection :=
    universalSocietySearchTypedRejection oldVisit sourceIndex (boundary + 1)

structure CanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrenceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  priorCofinalAntichain :
    CanonicalSocietyCofinalExternalPaymentLegislationAntichainAt oldVisit
      sourceIndex
  everyAcceptedLegislationEnacts : ∀ boundary
      {proposal : AnySourceBackedPaymentOccurrence}
      {legislation :
        TargetLegislationAt
          (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
            oldVisit sourceIndex boundary)}
      (acceptance :
        SourceAcceptedExternalPaymentLegislationAt
          (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
            oldVisit sourceIndex boundary)
          proposal legislation),
    AcceptedExternalPaymentLegislationEnactmentRecurrenceFactsAt acceptance
  everyCanonicalLegislationEnacts : ∀ boundary,
    AcceptedExternalPaymentLegislationEnactmentRecurrenceFactsAt
      (pointwiseAcceptanceAt oldVisit sourceIndex boundary)

theorem canonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrenceAt
      oldVisit sourceIndex where
  priorCofinalAntichain :=
    canonicalSocietyExternalPaymentLegislationAcceptance_cofinalAntichain
      oldVisit sourceIndex
  everyAcceptedLegislationEnacts := fun _boundary _proposal _legislation
      acceptance =>
    sourceAcceptedExternalPaymentLegislation_enactsAndGeneratesFreshNext
      acceptance
  everyCanonicalLegislationEnacts := fun boundary =>
    sourceAcceptedExternalPaymentLegislation_enactsAndGeneratesFreshNext
      (pointwiseAcceptanceAt oldVisit sourceIndex boundary)

structure CanonicalCofinalAcceptedExternalPaymentLegislationEnactmentRecurrenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) : Prop where
  priorPoint : CanonicalCofinalExternalPaymentLegislationAntichainAt point
  installedEnactmentRecurrence :
    CanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrenceAt
      oldVisit sourceIndex

theorem canonicalCofinalAcceptedExternalPaymentLegislationEnactmentRecurrence_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    CanonicalCofinalAcceptedExternalPaymentLegislationEnactmentRecurrenceAt
      point where
  priorPoint :=
    canonicalCofinalExternalPaymentLegislationAntichain_directConsumer point
  installedEnactmentRecurrence :=
    canonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence_directConsumer
      oldVisit sourceIndex

end
end M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence.sourceAcceptedExternalPaymentLegislation_enactsAndGeneratesFreshNext
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence.canonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence.canonicalCofinalAcceptedExternalPaymentLegislationEnactmentRecurrence_directConsumer
