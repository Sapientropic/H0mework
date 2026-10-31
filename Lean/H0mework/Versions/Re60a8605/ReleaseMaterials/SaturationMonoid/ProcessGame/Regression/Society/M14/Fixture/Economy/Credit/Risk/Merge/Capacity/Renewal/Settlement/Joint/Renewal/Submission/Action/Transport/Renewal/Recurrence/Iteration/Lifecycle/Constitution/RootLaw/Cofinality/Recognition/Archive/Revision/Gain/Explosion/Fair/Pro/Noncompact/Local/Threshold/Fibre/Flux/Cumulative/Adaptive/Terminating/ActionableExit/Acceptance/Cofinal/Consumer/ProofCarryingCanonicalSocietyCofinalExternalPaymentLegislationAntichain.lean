import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Consumer.ProofCarryingCanonicalSocietyAdaptiveExternalPaymentLegislationAcceptance
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Cofinal.Source.SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance

/-!
# Proof-carrying cofinal external-Payment legislation antichain

Every emitted replay is finitely recognized and source-accepted at its exact
Payment/PCL fibre.  The target map is globally injective.  Every finite
adaptive Payment policy is eventually constant, so on the cofinal source tail
it can be accepted at most one span and admits no dependent total section.
The actual paid-self-U8 recurrence nevertheless generates the next accepted
span at every boundary.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyCofinalExternalPaymentLegislationAntichain

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy.CanonicalPaidReplayFairFiniteAdaptivePolicy
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14ProofCarryingCanonicalSocietyAdaptiveExternalPaymentLegislationAcceptance
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance

/-- Maximum cofinal legislation-acceptance contract at one installed source. -/
structure CanonicalSocietyCofinalExternalPaymentLegislationAntichainAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  priorAdaptiveAcceptance :
    CanonicalSocietyAdaptiveExternalPaymentLegislationAcceptanceAt oldVisit
      sourceIndex
  targetInjective :
    Function.Injective
      (fun boundary =>
        targetAnyPaymentOccurrence
          (sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
            oldVisit sourceIndex boundary))
  everyPointwiseRecognizedTargetAccepted : ∀ boundary,
    type_of%
      (pointwiseRecognizedPaymentProposal_isSourceAccepted oldVisit sourceIndex
        boundary)
  everyAcceptanceFibreExact : ∀ boundary
      (span :
        SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex boundary)
      (proposal : AnySourceBackedPaymentOccurrence)
      (legislation : TargetLegislationAt span),
    Nonempty
        (SourceAcceptedExternalPaymentLegislationAt span proposal legislation) ↔
      proposal =
          pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex boundary ∧
        HEq legislation (targetLegislation span)
  everyCommonProposalFibreDisjoint : ∀ leftBoundary rightBoundary
      (different : leftBoundary ≠ rightBoundary)
      (proposal : AnySourceBackedPaymentOccurrence),
    type_of%
      (distinctExternalPaymentLegislationAcceptances_joint_isEmpty oldVisit
        sourceIndex leftBoundary rightBoundary different proposal)
  everyRecurrenceGeneratesNextAcceptance : ∀ boundary,
    type_of%
      (externalPaymentLegislationAcceptance_recurrence_closesNext oldVisit
        sourceIndex boundary)
  everyFiniteAdaptivePolicyGeneratesCofinalAntichain : ∀ requestedStage fuel
      (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy
        AnySourceBackedPaymentOccurrence fuel),
    let cutoff := adaptivePolicyCutoff requestedStage policy
    requestedStage < cutoff ∧
      (∀ boundary, cutoff ≤ boundary →
        policy.run (rightReplayAt oldVisit sourceIndex boundary) =
          policy.zeroBranchAnswer) ∧
      (∀ leftBoundary rightBoundary,
        cutoff ≤ leftBoundary → cutoff ≤ rightBoundary →
        Nonempty
            (let span :=
              sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
                oldVisit sourceIndex leftBoundary
            SourceAcceptedExternalPaymentLegislationAt span
              (policy.run
                (rightReplayAt oldVisit sourceIndex leftBoundary))
              (targetLegislation span)) →
        Nonempty
            (let span :=
              sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
                oldVisit sourceIndex rightBoundary
            SourceAcceptedExternalPaymentLegislationAt span
              (policy.run
                (rightReplayAt oldVisit sourceIndex rightBoundary))
              (targetLegislation span)) →
        leftBoundary = rightBoundary) ∧
      IsEmpty
        ((tailBoundary : {boundary : Nat // cutoff ≤ boundary}) →
          let span :=
            sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
              oldVisit sourceIndex tailBoundary.1
          SourceAcceptedExternalPaymentLegislationAt span
            (policy.run
              (rightReplayAt oldVisit sourceIndex tailBoundary.1))
            (targetLegislation span)) ∧
      IsEmpty
        ((boundary : Nat) →
          let span :=
            sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
              oldVisit sourceIndex boundary
          SourceAcceptedExternalPaymentLegislationAt span
            (policy.run (rightReplayAt oldVisit sourceIndex boundary))
            (targetLegislation span))

/-- The source itself generates the full cofinal acceptance antichain. -/
theorem canonicalSocietyExternalPaymentLegislationAcceptance_cofinalAntichain
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CanonicalSocietyCofinalExternalPaymentLegislationAntichainAt oldVisit
      sourceIndex where
  priorAdaptiveAcceptance :=
    canonicalSocietyAdaptiveExternalPaymentLegislationAcceptance_directConsumer
      oldVisit sourceIndex
  targetInjective :=
    externalPaymentLegislationTarget_injective oldVisit sourceIndex
  everyPointwiseRecognizedTargetAccepted := fun boundary =>
    pointwiseRecognizedPaymentProposal_isSourceAccepted oldVisit sourceIndex
      boundary
  everyAcceptanceFibreExact := fun boundary span proposal legislation =>
    sourceAcceptance_nonempty_iff_pointwiseProposal_exactPCL span proposal
      legislation
  everyCommonProposalFibreDisjoint := fun leftBoundary rightBoundary different
      proposal =>
    distinctExternalPaymentLegislationAcceptances_joint_isEmpty oldVisit
      sourceIndex leftBoundary rightBoundary different proposal
  everyRecurrenceGeneratesNextAcceptance := fun boundary =>
    externalPaymentLegislationAcceptance_recurrence_closesNext oldVisit
      sourceIndex boundary
  everyFiniteAdaptivePolicyGeneratesCofinalAntichain := by
    intro requestedStage fuel policy
    let cutoff := adaptivePolicyCutoff requestedStage policy
    have requestedLt : requestedStage < cutoff :=
      requestedStage_lt_adaptivePolicyCutoff requestedStage policy
    have tailRun : ∀ boundary, cutoff ≤ boundary →
        policy.run (rightReplayAt oldVisit sourceIndex boundary) =
          policy.zeroBranchAnswer := by
      intro boundary boundaryLate
      apply policy.run_eq_zeroBranchAnswer_of_bound_lt
      have zeroLt : zeroBranchBound policy < cutoff :=
        zeroBranchBound_lt_adaptivePolicyCutoff requestedStage policy
      change zeroBranchBound policy < boundary + 2
      omega
    have atMostOne : ∀ leftBoundary rightBoundary,
        cutoff ≤ leftBoundary → cutoff ≤ rightBoundary →
        Nonempty
            (let span :=
              sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
                oldVisit sourceIndex leftBoundary
            SourceAcceptedExternalPaymentLegislationAt span
              (policy.run
                (rightReplayAt oldVisit sourceIndex leftBoundary))
              (targetLegislation span)) →
        Nonempty
            (let span :=
              sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
                oldVisit sourceIndex rightBoundary
            SourceAcceptedExternalPaymentLegislationAt span
              (policy.run
                (rightReplayAt oldVisit sourceIndex rightBoundary))
              (targetLegislation span)) →
        leftBoundary = rightBoundary := by
      intro leftBoundary rightBoundary leftLate rightLate leftAccepted
        rightAccepted
      let leftSpan :=
        sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex leftBoundary
      let rightSpan :=
        sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
          oldVisit sourceIndex rightBoundary
      change Nonempty
        (SourceAcceptedExternalPaymentLegislationAt leftSpan
          (policy.run (rightReplayAt oldVisit sourceIndex leftBoundary))
          (targetLegislation leftSpan)) at leftAccepted
      change Nonempty
        (SourceAcceptedExternalPaymentLegislationAt rightSpan
          (policy.run (rightReplayAt oldVisit sourceIndex rightBoundary))
          (targetLegislation rightSpan)) at rightAccepted
      rcases leftAccepted with ⟨leftAcceptance⟩
      rcases rightAccepted with ⟨rightAcceptance⟩
      apply externalPaymentLegislationTarget_injective oldVisit sourceIndex
      exact leftAcceptance.proposalExact.symm.trans
        ((tailRun leftBoundary leftLate).trans
          ((tailRun rightBoundary rightLate).symm.trans
            rightAcceptance.proposalExact))
    have noTotal :
        IsEmpty
          ((tailBoundary : {boundary : Nat // cutoff ≤ boundary}) →
            let span :=
              sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
                oldVisit sourceIndex tailBoundary.1
            SourceAcceptedExternalPaymentLegislationAt span
              (policy.run
                (rightReplayAt oldVisit sourceIndex tailBoundary.1))
              (targetLegislation span)) := by
      refine ⟨fun totalAcceptance => ?_⟩
      let leftBoundary : {boundary : Nat // cutoff ≤ boundary} :=
        ⟨cutoff, le_rfl⟩
      let rightBoundary : {boundary : Nat // cutoff ≤ boundary} :=
        ⟨cutoff + 1, by omega⟩
      have boundaryEquality : cutoff = cutoff + 1 :=
        atMostOne cutoff (cutoff + 1) le_rfl (by omega)
          ⟨totalAcceptance leftBoundary⟩
          ⟨totalAcceptance rightBoundary⟩
      omega
    have noGlobalTotal :
        IsEmpty
          ((boundary : Nat) →
            let span :=
              sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
                oldVisit sourceIndex boundary
            SourceAcceptedExternalPaymentLegislationAt span
              (policy.run (rightReplayAt oldVisit sourceIndex boundary))
              (targetLegislation span)) := by
      refine ⟨fun globalAcceptance => noTotal.false ?_⟩
      intro tailBoundary
      exact globalAcceptance tailBoundary.1
    exact ⟨requestedLt, tailRun, atMostOne, noTotal, noGlobalTotal⟩

/-- Compact same-point carrier retaining the previous accepted legislation
boundary and installing the cofinal antichain at that exact source. -/
structure CanonicalCofinalExternalPaymentLegislationAntichainAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) : Prop where
  priorPoint :
    CanonicalCofinalAdaptiveExternalPaymentLegislationAcceptanceAt point
  installedAntichain :
    CanonicalSocietyCofinalExternalPaymentLegislationAntichainAt oldVisit
      sourceIndex

/-- The exact constitutional point consumes the cofinal antichain without a
new Society sink. -/
theorem canonicalCofinalExternalPaymentLegislationAntichain_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    CanonicalCofinalExternalPaymentLegislationAntichainAt point where
  priorPoint :=
    canonicalCofinalAdaptiveExternalPaymentLegislationAcceptance_directConsumer
      point
  installedAntichain :=
    canonicalSocietyExternalPaymentLegislationAcceptance_cofinalAntichain
      oldVisit sourceIndex

end
end M14ProofCarryingCanonicalSocietyCofinalExternalPaymentLegislationAntichain
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyCofinalExternalPaymentLegislationAntichain.canonicalSocietyExternalPaymentLegislationAcceptance_cofinalAntichain
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyCofinalExternalPaymentLegislationAntichain.canonicalCofinalExternalPaymentLegislationAntichain_directConsumer
