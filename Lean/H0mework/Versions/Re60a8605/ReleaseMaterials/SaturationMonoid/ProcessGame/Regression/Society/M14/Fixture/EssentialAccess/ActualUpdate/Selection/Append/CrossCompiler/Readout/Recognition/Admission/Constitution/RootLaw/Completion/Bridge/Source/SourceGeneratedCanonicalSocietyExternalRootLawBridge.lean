import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Effect.Consumer.ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEffect

/-!
# General rooted-submission / external-Payment root-law bridge

An arbitrary rooted submission at the installed universal-Society visit has no
same-occurrence local legislation row.  Its exact source event nevertheless
lies at the post-root endpoint of the existing right replay.  That same replay
already generates the external Payment occurrence, installed proof-carrying
legislation, whole-ledger consumer, revolutionary self-U8 and runtime next.

This bridge changes only the source submission parameter.  The target Payment,
entry, execution, ledger, U8 core and next remain the existing canonical
objects; the two root occurrences remain provably distinct.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyExternalRootLawBridge

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal Legislation UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEffect

universe uVisible uOutput uEffect

/-- Exact bridge from any rooted raw submission at one installed M14 visit to
the already generated external Payment legislation effect. -/
structure SourceGeneratedCanonicalSocietyExternalRootLawBridgeAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex boundary) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material)
    (rooted : SourceNativeObserverConsumerRootedAuthorityAt generated) :
    Type (max 31 (uVisible + 1) (uOutput + 1) (uEffect + 1)) where
  private mk ::
  transport :
    SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  transportExact : transport =
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  sourceRooted : SourceNativeObserverConsumerRootedAuthorityAt generated
  sourceEventExact : generated.exactEvent =
    (transport.sourceSubmission).exactEvent
  sourceRootLedgerAndNext : type_of% generated.rootLedgerAndNext_factorize
  sourceLocalLegislationEmpty :
    IsEmpty (SourceNativeObserverConsumerSameOccurrenceLegislationAt generated)
  sourceTargetOccurrencesDistinct :
    Sum.inl generated.exactEvent ≠
      Sum.inr (transport.targetPaymentOccurrence).rootOccurrence
  targetPaymentRootExact :
    type_of% transport.targetPaymentRootOccurrenceExact
  targetEntryAuthority : type_of% transport.targetEntryAuthority
  targetExecution : type_of% transport.targetExecution
  targetLegislation : type_of% transport.targetLegislation
  targetConsumer : type_of% transport.targetConsumer
  targetSelfU8 : type_of% transport.targetSelfU8
  targetFailureExact :
    (transport.targetSelfU8).failure =
      RootInquiryU8CompletionRegression.failure
  targetPaymentAndLegislationShareRow :
    type_of% transport.targetPaymentAndLegislation_shareRow
  targetLegislationOccurrenceIsPayment :
    type_of% transport.targetLegislationOccurrence_isPaymentOccurrence
  targetCoreIsInstalledAugmentedCore : type_of% transport.targetCore_isAugmentedCore
  targetRuntimeConsumesInstalledCore :
    type_of% transport.targetRuntimeConsumesAugmentedCore
  targetEffect : AcceptedExternalPaymentLegislationEffectFactsAt
    (pointwiseAcceptanceAt oldVisit sourceIndex boundary)
  targetEffectConsumerExact : HEq
    (pointwiseAcceptanceAt oldVisit sourceIndex boundary).independentConsumer
    transport.targetConsumer

/-- The local fibre is empty for every raw submission at this physical visit,
not only for the canonical identity-observer program. -/
theorem arbitrarySourceLocalLegislation_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex boundary) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    IsEmpty (SourceNativeObserverConsumerSameOccurrenceLegislationAt generated) :=
  emptyLocalLedger_sameOccurrenceLegislation_isEmpty generated
    ((rightReplayAt oldVisit sourceIndex boundary).2.payment
      ).occurrenceLocalLedgerEmpty

theorem arbitrarySourceTargetOccurrencesDistinct
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex boundary) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material)
    (transport :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    Sum.inl generated.exactEvent ≠
      Sum.inr (transport.targetPaymentOccurrence).rootOccurrence := by
  intro collapse
  apply transport.sourceTargetOccurrencesDistinct
  simp at collapse

/-- Sole bridge producer.  The only operational inputs beyond the existing
M14 indices are the already generated raw submission and its rooted authority;
no target object is accepted. -/
def sourceGeneratedCanonicalSocietyExternalRootLawBridge
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex boundary) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material)
    (rooted : SourceNativeObserverConsumerRootedAuthorityAt generated) :
    SourceGeneratedCanonicalSocietyExternalRootLawBridgeAt generated rooted := by
  let transport :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  exact
    { transport := transport
      transportExact := rfl
      sourceRooted := rooted
      sourceEventExact := rfl
      sourceRootLedgerAndNext := generated.rootLedgerAndNext_factorize
      sourceLocalLegislationEmpty :=
        arbitrarySourceLocalLegislation_isEmpty generated
      sourceTargetOccurrencesDistinct :=
        arbitrarySourceTargetOccurrencesDistinct generated transport
      targetPaymentRootExact := transport.targetPaymentRootOccurrenceExact
      targetEntryAuthority := transport.targetEntryAuthority
      targetExecution := transport.targetExecution
      targetLegislation := transport.targetLegislation
      targetConsumer := transport.targetConsumer
      targetSelfU8 := transport.targetSelfU8
      targetFailureExact :=
        M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.selfU8_failure_isExistingM9Failure
          transport.targetExecution
      targetPaymentAndLegislationShareRow :=
        transport.targetPaymentAndLegislation_shareRow
      targetLegislationOccurrenceIsPayment :=
        transport.targetLegislationOccurrence_isPaymentOccurrence
      targetCoreIsInstalledAugmentedCore := transport.targetCore_isAugmentedCore
      targetRuntimeConsumesInstalledCore :=
        transport.targetRuntimeConsumesAugmentedCore
      targetEffect :=
        sourceAcceptedExternalPaymentLegislation_enactsExactEffect
          (pointwiseAcceptanceAt oldVisit sourceIndex boundary)
      targetEffectConsumerExact :=
        (sourceAcceptedExternalPaymentLegislation_enactsExactEffect
          (pointwiseAcceptanceAt oldVisit sourceIndex boundary)
          ).acceptedConsumerExact }

/-- Existential spelling used by the final raw-attempt exhaustion theorem. -/
abbrev RootedExternalRootLawAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex boundary) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :=
  Sigma fun rooted : SourceNativeObserverConsumerRootedAuthorityAt generated =>
    SourceGeneratedCanonicalSocietyExternalRootLawBridgeAt generated rooted

end
end M14SourceGeneratedCanonicalSocietyExternalRootLawBridge
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalRootLawBridge.arbitrarySourceTargetOccurrencesDistinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalRootLawBridge.arbitrarySourceLocalLegislation_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalRootLawBridge.sourceGeneratedCanonicalSocietyExternalRootLawBridge
