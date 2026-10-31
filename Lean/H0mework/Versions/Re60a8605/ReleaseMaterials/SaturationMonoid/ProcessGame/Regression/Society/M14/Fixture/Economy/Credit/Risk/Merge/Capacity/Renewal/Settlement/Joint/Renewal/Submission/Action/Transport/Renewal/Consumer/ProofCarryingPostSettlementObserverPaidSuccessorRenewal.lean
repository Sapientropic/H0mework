import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Morphism.Consumer.ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Producer.SourceGeneratedPostSettlementObserverPaidSuccessorRenewal

/-!
# Proof-carrying no-free observer authority and fresh paid successor

This consumer joins the negative and positive halves of authority renewal.
The revised first-row observer coordinate has no later installation at any
positive depth.  The exact morphism span nevertheless selects an existing
paid successor whose source event and Payment are definitionally the same
span endpoints.  That successor regenerates action authority and K from its
own occurrence, carries an independent consumer and factorized next, and
rejects an unrenewed source-as-target replay.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal.SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
open M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal

structure ProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    (morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority) : Prop where
  private mk ::
  morphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      morphism
  noLaterObserverReplay : ∀ laterIndex : Nat,
    IsEmpty
      (SourceInstalledRenewalAt
        (renewalRecognitionAt oldVisit sourceIndex boundary)
        (revisedTemporalVisitAt oldVisit sourceIndex boundary
          (laterIndex + 1)))
  firstSuccessorExact : HEq
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.successor
    (generatedFirstSuccessorAt oldVisit sourceIndex boundary)
  sourceEventExact :
    (paidRenewalAt morphism).sourceConsequence.outerRootEvent =
      (sourceSubmission (legislationSpan morphism)).exactEvent
  sourcePaymentExact :
    (paidRenewalAt morphism).sourceConsequence.actualExit.paymentOccurrence =
      targetPaymentOccurrence (legislationSpan morphism)
  paidRenewalExact : PaidSuccessorRenewalExactAt morphism
  unrenewedReplayEmpty :
    IsEmpty
      (ExactPaidSuccessorBearerExerciseStandingUnrenewedReplayAt oldVisit
        sourceIndex (paidIndexAt morphism))
  targetInstalledExact :
    targetInstalledRenewal morphism =
      installedUBIAt (paidRenewalAt morphism).targetAuthorityCurrent
  targetRootFactorization :
    (targetInstalledRenewal morphism).RootAnswerAndNextFactorizes
  targetResponsibilityConsumer :
    Nonempty
      (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        (paidRenewalAt morphism).targetConsequence.actualExit)
  targetOwnRootReadAuthority :
    Nonempty
      (PostSettlementPaymentBearerExerciseCarrierAt
        (paidRenewalAt morphism).targetConsequence.outerRootEvent)
  targetActionExact :
    (paidRenewalAt morphism).targetConsequence.exerciseAction =
      birthBearerExactExitExerciseAction
  targetContinues : TargetPaidOccurrenceContinuesAt morphism

/-- Independent direct consumer of one morphism-indexed paid renewal. -/
theorem proofCarryingPostSettlementObserverPaidSuccessorRenewal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    (morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority) :
    ProofCarryingPostSettlementObserverPaidSuccessorRenewalAt morphism where
  morphismCertificate :=
    proofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
      morphism
  noLaterObserverReplay := fun laterIndex =>
    firstRowObserverRenewal_afterSuccessor_isEmpty
      (oldVisit := oldVisit) (sourceIndex := sourceIndex)
      (boundary := boundary) laterIndex
  firstSuccessorExact :=
    (firstSuccessorAndNoObserverReplay morphism 0).1
  sourceEventExact := paidRenewal_sourceEvent_isSpanSourceEvent morphism
  sourcePaymentExact := paidRenewal_sourcePayment_isSpanTargetPayment morphism
  paidRenewalExact := paidSuccessorRenewal_exact morphism
  unrenewedReplayEmpty := paidSuccessorUnrenewedReplay_isEmpty morphism
  targetInstalledExact := targetInstalledRenewal_exact morphism
  targetRootFactorization := targetInstalledRenewal_rootFactorizes morphism
  targetResponsibilityConsumer :=
    targetInstalledRenewal_hasConsumer morphism
  targetOwnRootReadAuthority := (targetOwnRootReadAction morphism).1
  targetActionExact := (targetOwnRootReadAction morphism).2
  targetContinues := targetPaidOccurrenceContinues morphism

/-- Closed previous morphism package plus its no-free/fresh-renewal direct
consumer. -/
abbrev AnyProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { carried :
      AnyProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        oldVisit sourceIndex boundary //
    ProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
      carried.2.2.1 }

def canonicalProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AnyProofCarryingPostSettlementObserverPaidSuccessorRenewalAt oldVisit
      sourceIndex boundary :=
  let carried :=
    canonicalProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      oldVisit sourceIndex boundary
  ⟨carried,
    proofCarryingPostSettlementObserverPaidSuccessorRenewal
      carried.2.2.1⟩

end
end M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal.proofCarryingPostSettlementObserverPaidSuccessorRenewal
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal.canonicalProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
