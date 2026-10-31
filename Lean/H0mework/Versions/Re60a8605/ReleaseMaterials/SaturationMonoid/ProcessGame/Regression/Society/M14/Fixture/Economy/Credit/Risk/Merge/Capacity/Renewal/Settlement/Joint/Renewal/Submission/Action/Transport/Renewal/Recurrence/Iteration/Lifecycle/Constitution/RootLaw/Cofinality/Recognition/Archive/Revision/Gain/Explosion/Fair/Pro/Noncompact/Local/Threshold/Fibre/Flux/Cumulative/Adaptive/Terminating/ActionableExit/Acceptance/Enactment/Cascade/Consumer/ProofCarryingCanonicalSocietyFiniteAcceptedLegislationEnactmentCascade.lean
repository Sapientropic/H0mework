import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Step.Source.SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep

/-!
# Proof-carrying finite accepted-legislation enactment cascade

Every finite audit consumes the existing physical `cycleAt` fold and paid-exit
lifecycle stitch.  Its generated final next is accepted, enacted and still
extends by another actual recurrence step.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance
open M14ProofCarryingCanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence
open M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
open M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep

theorem cyclePointwiseRecognizedPaymentProposal_injective
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    Function.Injective
      (fun node : Fin (fuel + 1) =>
        pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + node.1)) := by
  intro left right proposalEquality
  let leftSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + left.1)
  let rightSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + right.1)
  have leftExact :=
    pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
      (boundary + left.1) leftSpan
  have rightExact :=
    pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
      (boundary + right.1) rightSpan
  have boundaryEquality : boundary + left.1 = boundary + right.1 :=
    externalPaymentLegislationTarget_injective oldVisit sourceIndex
      (leftExact.symm.trans (proposalEquality.trans rightExact))
  apply Fin.ext
  omega

/-- Full finite physical cascade with exact node, edge and terminal-next
responsibilities. -/
structure ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascadeAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop where
  priorOneStepEnactment :
    CanonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrenceAt
      oldVisit sourceIndex
  priorFiniteLifecycle :
    ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt initial
      fuel
  everyNodeEffect : ∀ node : Fin (fuel + 1),
    CycleAcceptedLegislationEffectFactsAt initial node.1
  everyEdgeUsesLiteralGeneratedSpan : ∀ edge : Fin fuel,
    cycleLegislationSpanAt initial (edge.1 + 1) =
      nextSpan (stepAt initial edge.1)
  everyEdgeActualEnactmentRecurrence : ∀ edge : Fin fuel,
    CycleAcceptedLegislationStepFactsAt initial edge.1
  nodeProposalsInjective :
    Function.Injective
      (fun node : Fin (fuel + 1) =>
        pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + node.1))
  finalGeneratedNextCycleExact :
    generatedFinalNextCycleAt initial fuel = cycleAt initial (fuel + 1)
  finalGeneratedNextSpanExact :
    (generatedFinalNextCycleAt initial fuel).1 =
      cycleLegislationSpanAt initial (fuel + 1)
  finalGeneratedNextAcceptance :
    Nonempty
      (SourceAcceptedExternalPaymentLegislationAt
        (generatedFinalNextCycleAt initial fuel).1
        (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + (fuel + 1)))
        (targetLegislation (generatedFinalNextCycleAt initial fuel).1))
  finalGeneratedNextEffect :
    CycleAcceptedLegislationEffectFactsAt initial (fuel + 1)
  finalGeneratedNextStillExtends :
    CycleAcceptedLegislationStepFactsAt initial (fuel + 1)

theorem proofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascadeAt
      initial fuel where
  priorOneStepEnactment :=
    canonicalSocietyAcceptedExternalPaymentLegislationEnactmentRecurrence_directConsumer
      oldVisit sourceIndex
  priorFiniteLifecycle :=
    proofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch initial
      fuel
  everyNodeEffect := fun node =>
    cycleAcceptedLegislationEffect initial node.1
  everyEdgeUsesLiteralGeneratedSpan := fun edge =>
    cycleLegislationSpan_succ_isStepNextSpan initial edge.1
  everyEdgeActualEnactmentRecurrence := fun edge =>
    cycleAcceptedLegislationStep initial edge.1
  nodeProposalsInjective :=
    cyclePointwiseRecognizedPaymentProposal_injective initial fuel
  finalGeneratedNextCycleExact :=
    generatedFinalNextCycle_eq_cycleAt_succ initial fuel
  finalGeneratedNextSpanExact := by
    rw [generatedFinalNextCycle_eq_cycleAt_succ]
  finalGeneratedNextAcceptance := by
    rw [generatedFinalNextCycle_eq_cycleAt_succ]
    exact ⟨cyclePointwiseAcceptanceAt initial (fuel + 1)⟩
  finalGeneratedNextEffect :=
    cycleAcceptedLegislationEffect initial (fuel + 1)
  finalGeneratedNextStillExtends :=
    cycleAcceptedLegislationStep initial (fuel + 1)

/-- No finite physical prefix has a terminal law: its actual final next is
already accepted, enacted and extendable. -/
structure CanonicalSocietyAcceptedLegislationNoFiniteTerminalAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) : Prop where
  everyFiniteCascade : ∀ fuel,
    ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascadeAt
      initial fuel

theorem canonicalSocietyAcceptedLegislationNoFiniteTerminal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    CanonicalSocietyAcceptedLegislationNoFiniteTerminalAt initial where
  everyFiniteCascade := fun fuel =>
    proofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
      initial fuel

end
end M14ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade.cyclePointwiseRecognizedPaymentProposal_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade.proofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade.canonicalSocietyAcceptedLegislationNoFiniteTerminal
