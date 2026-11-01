import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Renewal.Producer.SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Consequence.ProofCarryingBearerActionPaidConsequenceIndependentNecessityRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Preservation.PostSettlement.Step.Consumer.ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep

/-!
# Direct consumer of paid-successor bearer exercise standing renewal

This certificate consumes both action-bearing Payments, the source Payment's
canonical paid step, the target Payment's own root read, the equality of local
action content, the strict outer-occurrence and actual-service-K changes, both
external consumers, and the exact empty replay fibre.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPaidSuccessorBearerExerciseStandingRenewalRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
open M14ProofCarryingContributionCapacityPostSettlementCanonicalPaidStep
open M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity
open M14ProofCarryingBearerActionPaidConsequenceIndependentNecessityRegression
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal

abbrev CanonicalPaidSuccessorBearerExerciseStandingRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex index

def canonicalPaidSuccessorBearerExerciseStandingRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit sourceIndex
      index :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex index

structure PaidSuccessorBearerExerciseStandingRenewalAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (renewal : CanonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
      sourceIndex index) : Prop where
  canonicalExact : renewal =
    canonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit sourceIndex
      index
  sourceConsequenceExact : renewal.sourceConsequence =
    exactBearerActionPaidConsequenceAt oldVisit sourceIndex index
  targetConsequenceExact : renewal.targetConsequence =
    exactBearerActionPaidConsequenceAt oldVisit sourceIndex (index + 1)
  paidStepConsumed : Nonempty
    (ProofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
      renewal.paidStep)
  sourceAndTargetPaymentAlignment :
    renewal.sourcePayment = renewal.paidStep.sourcePayment ∧
      renewal.targetPayment = renewal.paidStep.targetPayment ∧
      renewal.targetConsequence.outerRootEvent =
        renewal.paidStep.targetRootEvent
  paidNextTargetsRenewedOuterOccurrence :
    HEq renewal.sourcePayment.nextPaidBy
      renewal.targetConsequence.outerRootEvent.occurrence
  ownRootReadIncidence :
    HEq renewal.sourceConsequence.exerciseRootRead
        renewal.sourcePayment.exerciseRootRead ∧
      HEq renewal.targetConsequence.exerciseRootRead
        renewal.targetPayment.exerciseRootRead ∧
      renewal.sourceConsequence.exerciseCarrier =
        Classical.choice renewal.sourceConsequence.exerciseRootRead.down ∧
      renewal.targetConsequence.exerciseCarrier =
        Classical.choice renewal.targetConsequence.exerciseRootRead.down ∧
      renewal.sourceConsequence.exerciseAction =
        renewal.sourceConsequence.exerciseCarrier.exitExerciseAction ∧
      renewal.targetConsequence.exerciseAction =
        renewal.targetConsequence.exerciseCarrier.exitExerciseAction
  sameLocalActionContent :
    renewal.sourceConsequence.exerciseAction =
        renewal.targetConsequence.exerciseAction ∧
      renewal.sourceConsequence.exerciseAction =
        birthBearerExactExitExerciseAction
  paymentIncidence :
    renewal.sourcePayment.exerciseFace.projection =
          ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      renewal.targetPayment.exerciseFace.projection =
          ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      birthBearerExitExerciseController.ControllerAt
          renewal.sourcePayment.exerciseAction birthBearerWorker ∧
      birthBearerExitExerciseController.ControllerAt
          renewal.targetPayment.exerciseAction birthBearerWorker
  adjacentAuthorityCurrents :
    renewal.targetAuthorityCurrent = renewal.sourceAuthorityCurrent + 1 ∧
      renewal.sourceAuthorityCurrent < renewal.targetAuthorityCurrent
  sourceOuterAuthorityCanonical : renewal.sourceOuterAuthority =
    contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit sourceIndex
      renewal.sourceAuthorityCurrent
  targetOuterAuthorityCanonical : renewal.targetOuterAuthority =
    contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit sourceIndex
      renewal.targetAuthorityCurrent
  outerAuthorityRenewed :
    renewal.sourceOuterAuthority ≠ renewal.targetOuterAuthority
  sourceActualServiceKCanonical : renewal.sourceActualServiceK =
    contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt
      oldVisit sourceIndex renewal.sourceAuthorityCurrent
  targetActualServiceKCanonical : renewal.targetActualServiceK =
    contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt
      oldVisit sourceIndex renewal.targetAuthorityCurrent
  actualServiceKPaymentAlignment :
    renewal.sourceActualServiceK.2.actualExit =
        renewal.sourceConsequence.actualExit ∧
      renewal.targetActualServiceK.2.actualExit =
        renewal.targetConsequence.actualExit
  actualServiceKRenewed :
    renewal.sourceActualServiceK ≠ renewal.targetActualServiceK
  bothRootReadAuthoritiesNonempty :
    Nonempty
        (PostSettlementPaymentBearerExerciseCarrierAt
          renewal.sourceConsequence.outerRootEvent) ∧
      Nonempty
        (PostSettlementPaymentBearerExerciseCarrierAt
          renewal.targetConsequence.outerRootEvent)
  bothExternalConsumers :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          renewal.sourceConsequence.actualExit) ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          renewal.targetConsequence.actualExit)
  bothLocalLedgersEmpty :
    IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          renewal.sourceConsequence.outerRootEvent.occurrence.1) ∧
      IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          renewal.targetConsequence.outerRootEvent.occurrence.1)
  targetContinues :
    renewal.targetConsequence.nativeWrite = renewal.targetPayment.write ∧
      HEq renewal.targetConsequence.externalLiability
        renewal.targetPayment.liability ∧
      HEq renewal.targetConsequence.successor
        renewal.targetPayment.successor ∧
      renewal.targetPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (renewal.targetAuthorityCurrent + 1)
  unrenewedReplayEmpty : IsEmpty
    (ExactPaidSuccessorBearerExerciseStandingUnrenewedReplayAt oldVisit
      sourceIndex index)

theorem paidSuccessorBearerExerciseStandingRenewalAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidSuccessorBearerExerciseStandingRenewalAuditAt
      (canonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
        sourceIndex index) := by
  let renewal :=
    canonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit sourceIndex
      index
  let paidStepConsumer :=
    proofCarryingContributionCapacityPostSettlementCanonicalPaidStepConsumerAt
      renewal.paidStep
  have consumers := renewal.sourceAndTargetExternalConsumers
  exact
    { canonicalExact := rfl
      sourceConsequenceExact := rfl
      targetConsequenceExact := rfl
      paidStepConsumed := ⟨paidStepConsumer⟩
      sourceAndTargetPaymentAlignment :=
        ⟨renewal.sourcePayment_isPaidStepSource,
          renewal.targetPayment_isPaidStepTarget,
          renewal.targetRootEvent_isPaidStepTarget⟩
      paidNextTargetsRenewedOuterOccurrence :=
        renewal.sourcePaidNext_isTargetOuterOccurrence
      ownRootReadIncidence := renewal.sourceAndTargetOwnRootReadIncidence
      sameLocalActionContent :=
        ⟨renewal.sourceAction_eq_targetAction,
          renewal.sourceAction_eq_canonical⟩
      paymentIncidence := renewal.sourceAndTargetPaymentIncidence
      adjacentAuthorityCurrents :=
        ⟨renewal.targetAuthorityCurrent_eq_source_add_one,
          renewal.sourceAuthorityCurrent_lt_target⟩
      sourceOuterAuthorityCanonical :=
        renewal.sourceOuterAuthority_eq_canonical
      targetOuterAuthorityCanonical :=
        renewal.targetOuterAuthority_eq_canonical
      outerAuthorityRenewed := renewal.sourceOuterAuthority_ne_target
      sourceActualServiceKCanonical := rfl
      targetActualServiceKCanonical := rfl
      actualServiceKPaymentAlignment :=
        ⟨renewal.sourceActualServiceK_actualExit_eq_payment,
          renewal.targetActualServiceK_actualExit_eq_payment⟩
      actualServiceKRenewed := renewal.sourceActualServiceK_ne_target
      bothRootReadAuthoritiesNonempty :=
        ⟨renewal.sourceRootReadAuthority_nonempty,
          renewal.targetRootReadAuthority_nonempty⟩
      bothExternalConsumers := consumers
      bothLocalLedgersEmpty := renewal.sourceAndTargetLocalLedgers_empty
      targetContinues := renewal.targetPaymentContinues
      unrenewedReplayEmpty :=
        paidSuccessorBearerExerciseStandingUnrenewedReplay_isEmpty oldVisit
          sourceIndex index }

structure ProofCarryingPaidSuccessorBearerExerciseStandingRenewalCertificate :
    Prop where
  everyRenewal : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (CanonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
        sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    PaidSuccessorBearerExerciseStandingRenewalAuditAt
      (canonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
        sourceIndex index)
  everyUnrenewedReplayEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPaidSuccessorBearerExerciseStandingUnrenewedReplayAt oldVisit
          sourceIndex index)

theorem proofCarryingPaidSuccessorBearerExerciseStandingRenewalDirectConsumer :
    ProofCarryingPaidSuccessorBearerExerciseStandingRenewalCertificate where
  everyRenewal := fun oldVisit sourceIndex index =>
    ⟨canonicalPaidSuccessorBearerExerciseStandingRenewalAt oldVisit sourceIndex
      index⟩
  everyAudit := paidSuccessorBearerExerciseStandingRenewalAuditAt
  everyUnrenewedReplayEmpty :=
    paidSuccessorBearerExerciseStandingUnrenewedReplay_isEmpty

end
end M14ProofCarryingPaidSuccessorBearerExerciseStandingRenewalRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorBearerExerciseStandingRenewalRegression.paidSuccessorBearerExerciseStandingRenewalAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorBearerExerciseStandingRenewalRegression.proofCarryingPaidSuccessorBearerExerciseStandingRenewalDirectConsumer
