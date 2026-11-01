import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Cofinal.Consumer.ProofCarryingCanonicalSocietyCofinalExternalPaymentLegislationAntichain

/-!
# Acceptance-indexed external-Payment legislation consumer

The existing acceptance transports the exact Payment-side PCL consumer along
its own dependent legislation index.  No enactment carrier is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Legislation
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance

namespace M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt

/-- A real acceptance transports the existing target consumer to the
acceptance's own dependent legislation index. -/
def independentConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation : TargetLegislationAt span}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt span proposal legislation) :
    ProofCarryingLegislationConsumerAt legislation := by
  have legislationExact : legislation = targetLegislation span :=
    eq_of_heq acceptance.legislationExact
  subst legislation
  exact targetConsumer span

theorem independentConsumer_heq_targetConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation : TargetLegislationAt span}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt span proposal legislation) :
    HEq acceptance.independentConsumer (targetConsumer span) := by
  cases acceptance
  rfl

theorem independentConsumer_branchKind_isRevolution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation : TargetLegislationAt span}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt span proposal legislation) :
    acceptance.independentConsumer.branchKind = .revolution := by
  cases acceptance
  rfl

theorem independentConsumer_revolutionaryConsumption_heq_target
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation : TargetLegislationAt span}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt span proposal legislation) :
    HEq acceptance.independentConsumer.revolutionaryConsumption
      (some (targetRevolutionaryConsumption span)) := by
  cases acceptance
  rfl

theorem independentConsumer_generatedNext_isRuntimeNext
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {proposal : AnySourceBackedPaymentOccurrence}
    {legislation : TargetLegislationAt span}
    (acceptance :
      SourceAcceptedExternalPaymentLegislationAt span proposal legislation) :
    acceptance.independentConsumer.generatedNext =
      ((runtimeAt oldVisit sourceIndex boundary).stateAt 1
        ).engine.node.erase := by
  cases acceptance
  rfl

/-- Canonical pointwise-recognized acceptance as a direct source term. -/
abbrev pointwiseAcceptanceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let span :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary
    SourceAcceptedExternalPaymentLegislationAt span
      (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary)
      (targetLegislation span) := by
  dsimp only
  let span :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  rw [pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex boundary
    span]
  exact sourceAcceptedExternalPaymentLegislationAt span

end M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt

end
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt.independentConsumer_heq_targetConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt.independentConsumer_branchKind_isRevolution
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt.independentConsumer_revolutionaryConsumption_heq_target
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt.independentConsumer_generatedNext_isRuntimeNext
