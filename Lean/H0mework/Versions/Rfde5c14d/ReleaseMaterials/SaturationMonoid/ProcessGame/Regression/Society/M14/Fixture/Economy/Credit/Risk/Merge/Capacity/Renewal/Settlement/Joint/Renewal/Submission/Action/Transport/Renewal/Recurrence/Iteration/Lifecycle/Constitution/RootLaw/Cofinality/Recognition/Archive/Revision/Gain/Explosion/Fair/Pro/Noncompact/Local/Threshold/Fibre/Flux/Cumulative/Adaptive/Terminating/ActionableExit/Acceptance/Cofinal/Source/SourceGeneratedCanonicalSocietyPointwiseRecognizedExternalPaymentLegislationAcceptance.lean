import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Boundary.Source.SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary

/-!
# Pointwise-recognized external-Payment legislation acceptance

The already installed finite terminating recognizer derives the exact Payment
proposal for one emitted replay.  Source acceptance has an exact singleton
fibre at that proposal and the existing target PCL.  Across all source
boundaries the Payment targets are injective, and the existing paid-self-U8
recurrence generates the next accepted span.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14ProofCarryingUniversalObserverConsumerExhaustionRegression
open M14SourceGeneratedCanonicalSocietyPaidReplayFairPointwiseTerminatingRecognition
open M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyAdaptiveExternalPaymentLegislationBoundary

/-- The existing pointwise terminating recognizer derives a Payment proposal
from the authority of its recovered hot occurrence. -/
def pointwiseRecognizedPaymentProposalAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AnySourceBackedPaymentOccurrence :=
  (canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit sourceIndex
    (rightReplayAt oldVisit sourceIndex boundary)).2.authorityK.paymentOccurrence

/-- The recognized Payment proposal is exactly the existing source span
target; recognition does not create a new Payment occurrence. -/
theorem pointwiseRecognizedPaymentProposal_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary) :
    pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary =
      targetAnyPaymentOccurrence span := by
  change
    (canonicalPaidReplayFairTerminatingRecognizedOccurrence oldVisit
        sourceIndex
        (rightReplayAt oldVisit sourceIndex boundary)).2.authorityK.paymentOccurrence =
      (rightReplayAt oldVisit sourceIndex boundary).2.authorityK.paymentOccurrence
  exact congrArg
    (fun replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex =>
        replay.2.authorityK.paymentOccurrence)
    (canonicalPaidReplayFairTerminatingRecognizedOccurrence_exact oldVisit
      sourceIndex (rightReplayAt oldVisit sourceIndex boundary))

/-- The recognized source span retains the exact finite stopping stage. -/
theorem pointwiseRecognizedPaymentProposal_stopStage_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let replay := rightReplayAt oldVisit sourceIndex boundary
    let recognition :=
      sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
        sourceIndex replay
    recognition.stopStage = replay.1 + 1 ∧
      recognition.stopStage = boundary + 3 := by
  dsimp only
  let replay := rightReplayAt oldVisit sourceIndex boundary
  let recognition :=
    sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
      sourceIndex replay
  have stopExact : recognition.stopStage = replay.1 + 1 :=
    recognition.stopStageExact
  constructor
  · exact stopExact
  · rw [stopExact]
    change boundary + 2 + 1 = boundary + 3
    omega

/-- A recognized proposal is accepted by the exact source span while the
pointwise actionable-exit audit, PCL and typed search rejection remain live. -/
theorem pointwiseRecognizedPaymentProposal_isSourceAccepted
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let span :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary
    let replay := rightReplayAt oldVisit sourceIndex boundary
    let recognition :=
      sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
        sourceIndex replay
    pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary =
        targetAnyPaymentOccurrence span ∧
      recognition.stopStage = boundary + 3 ∧
      Nonempty
        (SourceAcceptedExternalPaymentLegislationAt span
          (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary)
          (targetLegislation span)) ∧
      type_of%
        (canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit
          sourceIndex replay) ∧
      type_of%
        (proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
          span) ∧
      type_of%
        (universalSocietySearchTypedRejection oldVisit sourceIndex boundary) ∧
      type_of% (targetAnyPaymentOccurrence_payload_heq span) := by
  dsimp only
  let span :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  let replay := rightReplayAt oldVisit sourceIndex boundary
  let recognition :=
    sourceGeneratedCanonicalPaidReplayFairTerminatingRecognition oldVisit
      sourceIndex replay
  have proposalExact :
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary =
        targetAnyPaymentOccurrence span :=
    pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex boundary span
  have accepted :
      Nonempty
        (SourceAcceptedExternalPaymentLegislationAt span
          (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary)
          (targetLegislation span)) := by
    rw [proposalExact]
    exact ⟨sourceAcceptedExternalPaymentLegislationAt span⟩
  exact
    ⟨proposalExact,
      pointwiseRecognizedPaymentProposal_stopStage_exact oldVisit sourceIndex
        boundary |>.2,
      accepted,
      canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit sourceIndex
        replay,
      proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
        span,
      universalSocietySearchTypedRejection oldVisit sourceIndex boundary,
      targetAnyPaymentOccurrence_payload_heq span⟩

/-- Exact singleton-fibre classification of source acceptance. -/
theorem sourceAcceptance_nonempty_iff_pointwiseProposal_exactPCL
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary)
    (proposal : AnySourceBackedPaymentOccurrence)
    (legislation : TargetLegislationAt span) :
    Nonempty
        (SourceAcceptedExternalPaymentLegislationAt span proposal legislation) ↔
      proposal =
          pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary ∧
        HEq legislation (targetLegislation span) := by
  constructor
  · rintro ⟨acceptance⟩
    have recognizedExact :
        pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary =
          targetAnyPaymentOccurrence span := by
      exact pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
        boundary span
    exact
      ⟨acceptance.proposalExact.trans recognizedExact.symm,
        acceptance.legislationExact⟩
  · rintro ⟨proposalExact, legislationExact⟩
    have targetExact :
        pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary =
          targetAnyPaymentOccurrence span := by
      exact pointwiseRecognizedPaymentProposal_exact oldVisit sourceIndex
        boundary span
    have proposalTargetExact : proposal = targetAnyPaymentOccurrence span :=
      proposalExact.trans targetExact
    have legislationEq : legislation = targetLegislation span :=
      eq_of_heq legislationExact
    subst proposal
    subst legislation
    exact ⟨sourceAcceptedExternalPaymentLegislationAt span⟩

/-- Exact Payment targets are injective over every source boundary. -/
theorem externalPaymentLegislationTarget_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (fun boundary =>
        targetAnyPaymentOccurrence
          (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
            oldVisit sourceIndex boundary)) := by
  intro leftBoundary rightBoundary paymentEquality
  have replayEquality :=
    canonicalPaidReplay_actionableExitPayment_injective oldVisit sourceIndex
      paymentEquality
  have depthEquality := congrArg Sigma.fst replayEquality
  change leftBoundary + 2 = rightBoundary + 2 at depthEquality
  omega

/-- One common proposal cannot be source-accepted at two distinct spans. -/
theorem distinctExternalPaymentLegislationAcceptances_joint_isEmpty
    (oldVisit : OldVisit) (sourceIndex leftBoundary rightBoundary : Nat)
    (different : leftBoundary ≠ rightBoundary)
    (proposal : AnySourceBackedPaymentOccurrence) :
    let leftSpan :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex leftBoundary
    let rightSpan :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex rightBoundary
    IsEmpty
      (SourceAcceptedExternalPaymentLegislationAt leftSpan proposal
            (targetLegislation leftSpan) ×
        SourceAcceptedExternalPaymentLegislationAt rightSpan proposal
          (targetLegislation rightSpan)) := by
  dsimp only
  let leftSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex leftBoundary
  let rightSpan :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex rightBoundary
  refine ⟨fun acceptances => different ?_⟩
  apply externalPaymentLegislationTarget_injective oldVisit sourceIndex
  exact acceptances.1.proposalExact.symm.trans
    acceptances.2.proposalExact

/-- The actual paid-self-U8 recurrence generates the next accepted source
span, with exact paid target event and Payment seams. -/
theorem externalPaymentLegislationAcceptance_recurrence_closesNext
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let recurrence :=
      canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
        oldVisit sourceIndex boundary
    let next :=
      sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex (boundary + 1)
    nextSpan recurrence.2.1 = next ∧
      type_of% recurrence.2.2 ∧
      type_of% recurrence.2.2.paidTargetIsNextSourceEvent ∧
      type_of% recurrence.2.2.paidTargetIsNextSpanPayment ∧
      Nonempty
        (SourceAcceptedExternalPaymentLegislationAt next
          (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
            (boundary + 1))
          (targetLegislation next)) ∧
      type_of%
        (proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
          next) := by
  dsimp only
  let recurrence :=
    canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
      oldVisit sourceIndex boundary
  let next :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex (boundary + 1)
  have nextAccepted :
      Nonempty
        (SourceAcceptedExternalPaymentLegislationAt next
          (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
            (boundary + 1))
          (targetLegislation next)) :=
    (pointwiseRecognizedPaymentProposal_isSourceAccepted oldVisit sourceIndex
      (boundary + 1)).2.2.1
  exact
    ⟨rfl,
      recurrence.2.2,
      recurrence.2.2.paidTargetIsNextSourceEvent,
      recurrence.2.2.paidTargetIsNextSpanPayment,
      nextAccepted,
      proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
        next⟩

end
end M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance.pointwiseRecognizedPaymentProposal_isSourceAccepted
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance.sourceAcceptance_nonempty_iff_pointwiseProposal_exactPCL
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance.externalPaymentLegislationTarget_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance.distinctExternalPaymentLegislationAcceptances_joint_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance.externalPaymentLegislationAcceptance_recurrence_closesNext
