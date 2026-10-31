import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Consumer.Source.SourceGeneratedCanonicalSocietyAcceptedExternalPaymentLegislationConsumer

/-!
# Proof-carrying accepted external-Payment legislation effect

One acceptance exposes the actual PCL consumer, revolutionary self-U8 and
macro-next facts of the same Payment occurrence.  The compact `Prop` below is
logical packaging only, not an enactment carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEffect

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Legislation UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt

structure AcceptedExternalPaymentLegislationEffectFactsAt
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
  proposalExact : type_of% acceptance.proposalExact
  legislationExact : type_of% acceptance.legislationExact
  acceptedConsumerExact :
    type_of% acceptance.independentConsumer_heq_targetConsumer
  wholeLedgerWriteBack :
    Nonempty (type_of% acceptance.independentConsumer.wholeLedgerWriteBack)
  rootFactorization : type_of% acceptance.independentConsumer.rootFactorization
  inquiryReceipt :
    Nonempty (type_of% acceptance.independentConsumer.inquiryReceipt)
  revolutionaryBranch :
    type_of% acceptance.independentConsumer_branchKind_isRevolution
  generatedNextIsRuntimeNext :
    type_of% acceptance.independentConsumer_generatedNext_isRuntimeNext
  revolutionaryConsumptionExact :
    type_of% acceptance.independentConsumer_revolutionaryConsumption_heq_target
  selfU8RuntimeConsumesCore :
    type_of%
      (targetSelfU8
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)).runtime_consumes_core
  selfU8FirstWriteConsumes :
    Nonempty
      (type_of%
        (targetSelfU8
          (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
            oldVisit sourceIndex boundary)).firstWriteConsumes)
  selfU8RowsShareGeneratedNext :
    type_of%
      (targetSelfU8
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)).revised_rows_share_generatedNext
  selfU8RootFactorization :
    type_of%
      (targetSelfU8
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)).rootAnswerAndNext_factorizes
  selfU8SameOccurrenceAsPayment :
    type_of%
      (M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.selfU8_sameOccurrenceAsRightPayment
        (targetExecution
          (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
            oldVisit sourceIndex boundary)))
  legislationOccurrenceIsPayment :
    type_of%
      (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary).targetLegislationOccurrence_isPaymentOccurrence
  targetMacroNextExact :
    type_of%
      (canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex boundary).2.2.currentCertificate.morphismCertificate.targetMacroNextExact

theorem sourceAcceptedExternalPaymentLegislation_enactsExactEffect
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
    AcceptedExternalPaymentLegislationEffectFactsAt acceptance where
  proposalExact := acceptance.proposalExact
  legislationExact := acceptance.legislationExact
  acceptedConsumerExact :=
    acceptance.independentConsumer_heq_targetConsumer
  wholeLedgerWriteBack :=
    ⟨acceptance.independentConsumer.wholeLedgerWriteBack⟩
  rootFactorization := acceptance.independentConsumer.rootFactorization
  inquiryReceipt := ⟨acceptance.independentConsumer.inquiryReceipt⟩
  revolutionaryBranch :=
    acceptance.independentConsumer_branchKind_isRevolution
  generatedNextIsRuntimeNext :=
    acceptance.independentConsumer_generatedNext_isRuntimeNext
  revolutionaryConsumptionExact :=
    acceptance.independentConsumer_revolutionaryConsumption_heq_target
  selfU8RuntimeConsumesCore :=
    (targetSelfU8
      (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary)).runtime_consumes_core
  selfU8FirstWriteConsumes :=
    ⟨(targetSelfU8
      (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary)).firstWriteConsumes⟩
  selfU8RowsShareGeneratedNext :=
    (targetSelfU8
      (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary)).revised_rows_share_generatedNext
  selfU8RootFactorization :=
    (targetSelfU8
      (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary)).rootAnswerAndNext_factorizes
  selfU8SameOccurrenceAsPayment :=
    M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.selfU8_sameOccurrenceAsRightPayment
      (targetExecution
        (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary))
  legislationOccurrenceIsPayment :=
    (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary).targetLegislationOccurrence_isPaymentOccurrence
  targetMacroNextExact :=
    (canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
      oldVisit sourceIndex boundary).2.2.currentCertificate.morphismCertificate.targetMacroNextExact

end
end M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEffect
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEffect.sourceAcceptedExternalPaymentLegislation_enactsExactEffect
