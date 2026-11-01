import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Consumer.ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Recurrence.Consumer.ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence

/-!
# Physical-cycle accepted legislation enactment source

Every node is read from the existing recursive `cycleAt` fold.  Its exact
acceptance and effect are generated from that physical span, never by
reselecting an independent canonical boundary occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Legislation UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance

/-- Exact legislation span carried by the recursively generated physical
cycle node. -/
abbrev cycleLegislationSpanAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + depth) :=
  (cycleAt initial depth).1

/-- Pointwise-recognized acceptance on the literal physical cycle span. -/
abbrev cyclePointwiseAcceptanceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceAcceptedExternalPaymentLegislationAt
      (cycleLegislationSpanAt initial depth)
      (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + depth))
      (targetLegislation (cycleLegislationSpanAt initial depth)) := by
  rw [pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
    (boundary + depth) (cycleLegislationSpanAt initial depth)]
  exact sourceAcceptedExternalPaymentLegislationAt
    (cycleLegislationSpanAt initial depth)

/-- Compact actual-effect facts for one physical cycle node. -/
structure CycleAcceptedLegislationEffectFactsAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  acceptedConsumerExact :
    type_of%
      (cyclePointwiseAcceptanceAt initial depth
        ).independentConsumer_heq_targetConsumer
  wholeLedgerWriteBack :
    Nonempty
      (type_of%
        (cyclePointwiseAcceptanceAt initial depth
          ).independentConsumer.wholeLedgerWriteBack)
  rootFactorization :
    type_of%
      (cyclePointwiseAcceptanceAt initial depth
        ).independentConsumer.rootFactorization
  revolutionaryBranch :
    type_of%
      (cyclePointwiseAcceptanceAt initial depth
        ).independentConsumer_branchKind_isRevolution
  revolutionaryConsumptionExact :
    type_of%
      (cyclePointwiseAcceptanceAt initial depth
        ).independentConsumer_revolutionaryConsumption_heq_target
  generatedNextIsRuntimeNext :
    type_of%
      (cyclePointwiseAcceptanceAt initial depth
        ).independentConsumer_generatedNext_isRuntimeNext
  selfU8RuntimeConsumesCore :
    type_of%
      (targetSelfU8
        (cycleLegislationSpanAt initial depth)).runtime_consumes_core
  selfU8FirstWriteConsumes :
    Nonempty
      (type_of%
        (targetSelfU8
          (cycleLegislationSpanAt initial depth)).firstWriteConsumes)
  selfU8RowsShareGeneratedNext :
    type_of%
      (targetSelfU8
        (cycleLegislationSpanAt initial depth)).revised_rows_share_generatedNext
  selfU8RootFactorization :
    type_of%
      (targetSelfU8
        (cycleLegislationSpanAt initial depth)).rootAnswerAndNext_factorizes
  selfU8SameOccurrenceAsPayment :
    type_of%
      (M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.selfU8_sameOccurrenceAsRightPayment
        (targetExecution (cycleLegislationSpanAt initial depth)))
  legislationOccurrenceIsPayment :
    type_of%
      (cycleLegislationSpanAt initial depth
        ).targetLegislationOccurrence_isPaymentOccurrence
  physicalMacroNextExact :
    type_of%
      (proofCarryingPostSettlementObserverPaidSelfU8Recurrence
        (stepAt initial depth)).currentCertificate.morphismCertificate.targetMacroNextExact

/-- Source producer for one node's complete accepted enactment effect. -/
theorem cycleAcceptedLegislationEffect
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    CycleAcceptedLegislationEffectFactsAt initial depth where
  acceptedConsumerExact :=
    (cyclePointwiseAcceptanceAt initial depth
      ).independentConsumer_heq_targetConsumer
  wholeLedgerWriteBack :=
    ⟨(cyclePointwiseAcceptanceAt initial depth
      ).independentConsumer.wholeLedgerWriteBack⟩
  rootFactorization :=
    (cyclePointwiseAcceptanceAt initial depth
      ).independentConsumer.rootFactorization
  revolutionaryBranch :=
    (cyclePointwiseAcceptanceAt initial depth
      ).independentConsumer_branchKind_isRevolution
  revolutionaryConsumptionExact :=
    (cyclePointwiseAcceptanceAt initial depth
      ).independentConsumer_revolutionaryConsumption_heq_target
  generatedNextIsRuntimeNext :=
    (cyclePointwiseAcceptanceAt initial depth
      ).independentConsumer_generatedNext_isRuntimeNext
  selfU8RuntimeConsumesCore :=
    (targetSelfU8
      (cycleLegislationSpanAt initial depth)).runtime_consumes_core
  selfU8FirstWriteConsumes :=
    ⟨(targetSelfU8
      (cycleLegislationSpanAt initial depth)).firstWriteConsumes⟩
  selfU8RowsShareGeneratedNext :=
    (targetSelfU8
      (cycleLegislationSpanAt initial depth)).revised_rows_share_generatedNext
  selfU8RootFactorization :=
    (targetSelfU8
      (cycleLegislationSpanAt initial depth)).rootAnswerAndNext_factorizes
  selfU8SameOccurrenceAsPayment :=
    M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.selfU8_sameOccurrenceAsRightPayment
      (targetExecution (cycleLegislationSpanAt initial depth))
  legislationOccurrenceIsPayment :=
    (cycleLegislationSpanAt initial depth
      ).targetLegislationOccurrence_isPaymentOccurrence
  physicalMacroNextExact :=
    (proofCarryingPostSettlementObserverPaidSelfU8Recurrence
      (stepAt initial depth)).currentCertificate.morphismCertificate.targetMacroNextExact

end
end M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade.cycleAcceptedLegislationEffect
