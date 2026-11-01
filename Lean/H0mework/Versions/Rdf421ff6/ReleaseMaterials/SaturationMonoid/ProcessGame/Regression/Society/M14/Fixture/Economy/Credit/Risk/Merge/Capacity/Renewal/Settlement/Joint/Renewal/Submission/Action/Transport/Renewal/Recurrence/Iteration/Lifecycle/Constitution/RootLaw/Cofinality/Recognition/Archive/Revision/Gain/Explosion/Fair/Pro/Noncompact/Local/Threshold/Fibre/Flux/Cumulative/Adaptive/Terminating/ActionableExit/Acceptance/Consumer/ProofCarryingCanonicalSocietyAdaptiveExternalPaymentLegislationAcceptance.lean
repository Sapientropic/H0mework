import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Consumer.ProofCarryingCanonicalSocietyPaidReplayActionableExitAuditBoundary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Boundary.Source.SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary

/-!
# Proof-carrying adaptive external-Payment legislation acceptance

The existing actionable-exit audit boundary is strengthened in place with a
source-indexed acceptance type, its adjacent-target impossibility and the
actual/search plus paid-self-U8 continuation seams.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyAdaptiveExternalPaymentLegislationAcceptance

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy
open M14ProofCarryingCanonicalSocietyPaidReplayActionableExitAuditBoundary
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary

/-- Compact named carrier for the maximum installed acceptance consumer. -/
structure CanonicalSocietyAdaptiveExternalPaymentLegislationAcceptanceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  priorActionableExitBoundary :
    type_of%
      (canonicalSocietyPaidReplayActionableExitAuditBoundary_directConsumer
        oldVisit sourceIndex)
  everySourceSpanAccepted : ∀ boundary,
    let span :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary
    Nonempty
        (SourceAcceptedExternalPaymentLegislationAt span
          (targetAnyPaymentOccurrence span) (targetLegislation span)) ∧
      type_of% (targetAnyPaymentOccurrence_payload_heq span) ∧
      type_of%
        (proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
          span)
  everyFiniteAdaptiveProposalBoundary : ∀ requestedStage fuel
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy
      AnySourceBackedPaymentOccurrence fuel),
    type_of%
      (finiteAdaptivePaymentProposal_generatesExactLegislationBoundary oldVisit
        sourceIndex requestedStage policy)

/-- Maximum installed acceptance consumer. -/
theorem canonicalSocietyAdaptiveExternalPaymentLegislationAcceptance_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CanonicalSocietyAdaptiveExternalPaymentLegislationAcceptanceAt oldVisit
      sourceIndex where
  priorActionableExitBoundary :=
    canonicalSocietyPaidReplayActionableExitAuditBoundary_directConsumer
      oldVisit sourceIndex
  everySourceSpanAccepted := fun boundary =>
    let span :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary
    ⟨⟨sourceAcceptedExternalPaymentLegislationAt span⟩,
      targetAnyPaymentOccurrence_payload_heq span,
      proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
        span⟩
  everyFiniteAdaptiveProposalBoundary := fun requestedStage _fuel policy =>
    finiteAdaptivePaymentProposal_generatesExactLegislationBoundary oldVisit
      sourceIndex requestedStage policy

/-- Compact same-point carrier; naming it prevents downstream elaboration from
re-expanding the entire accumulated theorem conjunction. -/
structure CanonicalCofinalAdaptiveExternalPaymentLegislationAcceptanceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) : Prop where
  priorPoint :
    type_of%
      (canonicalCofinalPaidReplayActionableExitAuditBoundary_directConsumer
        point)
  installedAcceptance :
    CanonicalSocietyAdaptiveExternalPaymentLegislationAcceptanceAt oldVisit
      sourceIndex

/-- The same constitutional point consumes the acceptance boundary without a
new Society sink. -/
theorem canonicalCofinalAdaptiveExternalPaymentLegislationAcceptance_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    CanonicalCofinalAdaptiveExternalPaymentLegislationAcceptanceAt point where
  priorPoint :=
    canonicalCofinalPaidReplayActionableExitAuditBoundary_directConsumer point
  installedAcceptance :=
    canonicalSocietyAdaptiveExternalPaymentLegislationAcceptance_directConsumer
      oldVisit sourceIndex

end
end M14ProofCarryingCanonicalSocietyAdaptiveExternalPaymentLegislationAcceptance
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAdaptiveExternalPaymentLegislationAcceptance.canonicalSocietyAdaptiveExternalPaymentLegislationAcceptance_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyAdaptiveExternalPaymentLegislationAcceptance.canonicalCofinalAdaptiveExternalPaymentLegislationAcceptance_directConsumer
