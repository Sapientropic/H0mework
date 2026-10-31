import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Source.SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade

/-!
# Physical accepted-legislation enactment step

One edge is the literal `stepAt` recurrence of the existing finite fold.  Its
`nextSpan` is the successor cycle span and carries the fresh accepted effect.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14ProofCarryingUniversalObserverConsumerExhaustionRegression
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance
open M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade

/-- The successor physical cycle span is literally the recurrence output. -/
theorem cycleLegislationSpan_succ_isStepNextSpan
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleLegislationSpanAt initial (depth + 1) =
      nextSpan (stepAt initial depth) :=
  rfl

/-- Adjacent physical nodes carry distinct recognized Payment proposals. -/
theorem cyclePointwiseProposal_succ_ne
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + depth) ≠
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + (depth + 1)) := by
  intro proposalEquality
  let current :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + depth)
  let next :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + (depth + 1))
  have currentExact :=
    pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
      (boundary + depth) current
  have nextExact :=
    pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
      (boundary + (depth + 1)) next
  have boundaryEquality :
      boundary + depth = boundary + (depth + 1) :=
    externalPaymentLegislationTarget_injective oldVisit sourceIndex
      (currentExact.symm.trans (proposalEquality.trans nextExact))
  omega

/-- Compact actual recurrence facts for one physical edge. -/
structure CycleAcceptedLegislationStepFactsAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  currentEffect : CycleAcceptedLegislationEffectFactsAt initial depth
  recurrenceCertificate :
    type_of%
      (proofCarryingPostSettlementObserverPaidSelfU8Recurrence
        (stepAt initial depth))
  successorSpanExact :
    type_of% (cycleLegislationSpan_succ_isStepNextSpan initial depth)
  paidTargetIsNextSourceEvent :
    type_of%
      (proofCarryingPostSettlementObserverPaidSelfU8Recurrence
        (stepAt initial depth)).paidTargetIsNextSourceEvent
  paidTargetIsNextSpanPayment :
    type_of%
      (proofCarryingPostSettlementObserverPaidSelfU8Recurrence
        (stepAt initial depth)).paidTargetIsNextSpanPayment
  proposalFresh : type_of% (cyclePointwiseProposal_succ_ne initial depth)
  literalNextAcceptance :
    Nonempty
      (SourceAcceptedExternalPaymentLegislationAt
        (nextSpan (stepAt initial depth))
        (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + (depth + 1)))
        (targetLegislation (nextSpan (stepAt initial depth))))
  nextAcceptedConsumerExact :
    type_of%
      (cyclePointwiseAcceptanceAt initial
        (depth + 1)).independentConsumer_heq_targetConsumer
  nextEffect : CycleAcceptedLegislationEffectFactsAt initial (depth + 1)
  currentSearchTypedRejection :
    type_of%
      (universalSocietySearchTypedRejection oldVisit sourceIndex
        (boundary + depth))
  nextSearchTypedRejection :
    type_of%
      (universalSocietySearchTypedRejection oldVisit sourceIndex
        (boundary + (depth + 1)))

theorem cycleAcceptedLegislationStep
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    CycleAcceptedLegislationStepFactsAt initial depth where
  currentEffect := cycleAcceptedLegislationEffect initial depth
  recurrenceCertificate :=
    proofCarryingPostSettlementObserverPaidSelfU8Recurrence
      (stepAt initial depth)
  successorSpanExact :=
    cycleLegislationSpan_succ_isStepNextSpan initial depth
  paidTargetIsNextSourceEvent :=
    (proofCarryingPostSettlementObserverPaidSelfU8Recurrence
      (stepAt initial depth)).paidTargetIsNextSourceEvent
  paidTargetIsNextSpanPayment :=
    (proofCarryingPostSettlementObserverPaidSelfU8Recurrence
      (stepAt initial depth)).paidTargetIsNextSpanPayment
  proposalFresh := cyclePointwiseProposal_succ_ne initial depth
  literalNextAcceptance :=
    ⟨cyclePointwiseAcceptanceAt initial (depth + 1)⟩
  nextAcceptedConsumerExact :=
    (cyclePointwiseAcceptanceAt initial
      (depth + 1)).independentConsumer_heq_targetConsumer
  nextEffect := cycleAcceptedLegislationEffect initial (depth + 1)
  currentSearchTypedRejection :=
    universalSocietySearchTypedRejection oldVisit sourceIndex
      (boundary + depth)
  nextSearchTypedRejection :=
    universalSocietySearchTypedRejection oldVisit sourceIndex
      (boundary + (depth + 1))

end
end M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep.cycleLegislationSpan_succ_isStepNextSpan
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep.cycleAcceptedLegislationStep
