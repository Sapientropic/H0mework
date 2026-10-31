import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Execution.Producer.SourceGeneratedPaidSuccessorBearerLeaveExecution

/-!
# Paid-successor bearer role-independent continuation

The already executed target Payment generates its next canonical paid step.
That step, rather than a naked `index + 2`, lands on the successor outer
occurrence.  The successor Payment's own continuation root read supplies the
phase-zero independent-relation target future and its capture-adjusted
actionable exit.

The action content agrees with the prior `.t1/.leave` execution, while outer
authority and actual-service occurrence identity are renewed.  No claim is
made that the leave action caused either Payment.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerLeaveExecution
open M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorBearerLeaveExecution

/-- Zero-payload cross-current continuation certificate. -/
inductive SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 30
  | private sealed

def sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index :=
  .sealed

namespace SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (continuation :
    SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index)

include continuation

theorem eq_sealed :
    continuation =
      sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
        oldVisit sourceIndex index := by
  cases continuation
  rfl

def execution
    (_continuation :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :
    SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
      index :=
  sourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
    index

/-- The exact next paid step generated from the executed target Payment. -/
def paidContinuationStep
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  ((execution certificate).standingRenewal.paidStep).generatedNextPaidStep

def executedPayment
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (execution certificate).targetPayment

def successorRootEvent
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (paidContinuationStep certificate).targetRootEvent

def successorPayment
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (paidContinuationStep certificate).targetPayment

def successorContinuationFace
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (successorPayment certificate).continuationFace

def successorContinuationRootRead
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (successorPayment certificate).continuationRootRead

def successorContinuationCarrier
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (successorPayment certificate).continuationCarrier

def successorContinuationAction
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (successorPayment certificate).continuationAction

def successorActionableExit
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  (successorPayment certificate).continuationActionableExit

def successorChannel
    (certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index)
    (channel : EssentialAccessChannel) :=
  (paidContinuationStep certificate).targetChannel channel

/-- Existing one-step renewal at `index + 1`; used only for exact
index+1→index+2 authority/K distinction. -/
def successorStandingRenewal
    (_certificate :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex (index + 1)

theorem paidContinuationStep_source_isExecutedPayment :
    (paidContinuationStep continuation).sourcePayment =
      executedPayment continuation :=
  rfl

/-- The executed Payment itself generates the successor occurrence. -/
theorem executedPaidNext_isSuccessorOuterOccurrence :
    HEq (executedPayment continuation).nextPaidBy
      (successorRootEvent continuation).occurrence := by
  rw [← paidContinuationStep_source_isExecutedPayment continuation]
  exact (paidContinuationStep continuation).nextPaidBy_isTargetCanonicalOccurrence

theorem successorStandingRenewalPaymentsExact :
    (successorStandingRenewal continuation).sourcePayment =
        executedPayment continuation ∧
      (successorStandingRenewal continuation).targetPayment =
        successorPayment continuation :=
  ⟨rfl, rfl⟩

theorem executedAndSuccessorOuterAuthorities_distinct :
    (successorStandingRenewal continuation).sourceOuterAuthority ≠
      (successorStandingRenewal continuation).targetOuterAuthority :=
  (successorStandingRenewal continuation).sourceOuterAuthority_ne_target

theorem executedAndSuccessorActualServiceK_distinct :
    (successorStandingRenewal continuation).sourceActualServiceK ≠
      (successorStandingRenewal continuation).targetActualServiceK :=
  (successorStandingRenewal continuation).sourceActualServiceK_ne_target

/-- The successor Payment itself reads the continuation face/rootRead. -/
theorem successorOwnContinuationIncidence :
    (successorContinuationFace continuation).projection =
        ContributionCapacityPostSettlementRenewalProjection.bearerRoleIndependentContinuation ∧
      successorContinuationCarrier continuation =
        Classical.choice (successorContinuationRootRead continuation).down ∧
      successorContinuationAction continuation =
        (successorContinuationCarrier continuation).exerciseActionValue ∧
      successorContinuationAction continuation =
        (successorPayment continuation).executionAction ∧
      successorActionableExit continuation =
        (successorContinuationCarrier continuation).actionableExit ∧
      (successorActionableExit continuation).1 =
        (successorContinuationAction continuation).1 := by
  have incidence :=
    (successorPayment continuation).bearerRoleIndependentContinuation_exact
  exact ⟨incidence.1, incidence.2.1, incidence.2.2.1,
    incidence.2.2.2.1, incidence.2.2.2.2.1,
    incidence.2.2.2.2.2.1⟩

theorem successorContinuationAction_eq_canonical :
    successorContinuationAction continuation =
      birthBearerExactExitExerciseAction := by
  calc
    successorContinuationAction continuation =
        (successorContinuationCarrier continuation).exerciseActionValue :=
      (successorPayment continuation).continuationActionFromRootRead
    _ = birthBearerExactExitExerciseAction :=
      (successorContinuationCarrier continuation).response.exerciseActionExact

theorem successorAction_eq_executedAction :
    successorContinuationAction continuation =
      (execution continuation).targetExecutionAction :=
  (successorContinuationAction_eq_canonical continuation).trans
    (execution continuation).targetExecutionAction_eq_canonical.symm

/-- Phase-zero relation role and both the capture-adjusted exit and raw
domain-native future witness. -/
theorem successorRoleIndependentFutureExact :
    birthBearerExitRelationCompiler.phaseStep
          birthBearerIndependentExitRelation = 0 ∧
      birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
          .source = .independent ∧
      birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
          .target = .independent ∧
      (successorActionableExit continuation).1 =
        (successorContinuationAction continuation).1 ∧
      (∃ future : birthBearerExitRelationCompiler.FutureContinuationAt
          birthBearerIndependentExitRelation.1 .target
            (successorContinuationAction continuation).1,
        birthBearerExitRelationCompiler.FutureContinuationWitnessAt
          birthBearerIndependentExitRelation.1 .target
            (successorContinuationAction continuation).1 future) ∧
      (¬ birthBearerNoCapture.Captures
        (successorContinuationAction continuation).1) ∧
      IsEmpty BirthBearerIndependentExitFalseExecutionPower := by
  have carrier := successorContinuationCarrier continuation
  have actionFromRoot :=
    (successorPayment continuation).continuationActionFromRootRead
  exact
    ⟨(successorPayment continuation).continuationPhaseExact,
      (successorPayment continuation).continuationSourceRoleExact,
      (successorPayment continuation).continuationTargetRoleExact,
      (successorPayment continuation).continuationActionableCodeExact,
      (by
        change ∃ future :
            birthBearerExitRelationCompiler.FutureContinuationAt
              birthBearerIndependentExitRelation.1 .target
                (successorPayment continuation).continuationAction.1,
          birthBearerExitRelationCompiler.FutureContinuationWitnessAt
            birthBearerIndependentExitRelation.1 .target
              (successorPayment continuation).continuationAction.1 future
        rw [actionFromRoot]
        exact carrier.witnessedFutureContinuation),
      (successorPayment continuation).continuationActionUncaptured,
      carrier.independentRelationCannotBeExecution⟩

theorem successorInstalledCapacityOne :
    (birthBearerGeometryCompilerAt
      (successorStandingRenewal continuation).targetAuthorityCurrent
      ).actionableExitCapacity = 1 :=
  (successorPayment continuation).responseExactCapacity

theorem everySuccessorChannelServiceAndNext :
    ∀ channel : EssentialAccessChannel,
      let consumed := successorChannel continuation channel
      Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1 + 1) channel) ∧
        consumed.2.actualNext =
          (successorPayment continuation).nextPaidBy := by
  intro channel
  let consumed := successorChannel continuation channel
  exact ⟨⟨consumed⟩,
    consumed.2.paymentNext_is_consumerNext.symm⟩

theorem successorExternalConsumerSuccessorAndFurtherNext :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (paidContinuationStep continuation).targetCurrent.actualExit) ∧
      Nonempty
        (SourceNativeLedgerGeneratedSuccessorAt
          (successorRootEvent continuation).occurrence
          (successorRootEvent continuation).wholeLedgerWriteBack) ∧
      (successorPayment continuation).nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
              sourceIndex (index + 1 + 1) +
            1) := by
  have external :=
    (paidContinuationStep continuation).targetExternalPaymentAndConsumer_nonempty
  exact ⟨external.1, external.2,
    ⟨(successorPayment continuation).successor⟩, rfl⟩

/-- Main continuation seal. -/
theorem paidSuccessorBearerRoleIndependentContinuation_exact :
    HEq (executedPayment continuation).nextPaidBy
        (successorRootEvent continuation).occurrence ∧
      successorContinuationAction continuation =
        (execution continuation).targetExecutionAction ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerIndependentExitRelation = 0 ∧
      birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
          .target = .independent ∧
      Nonempty BirthBearerRoleIndependentActionableExit ∧
      (∃ future : birthBearerExitRelationCompiler.FutureContinuationAt
          birthBearerIndependentExitRelation.1 .target
            (successorContinuationAction continuation).1,
        birthBearerExitRelationCompiler.FutureContinuationWitnessAt
          birthBearerIndependentExitRelation.1 .target
            (successorContinuationAction continuation).1 future) ∧
      IsEmpty BirthBearerIndependentExitFalseExecutionPower ∧
      (successorStandingRenewal continuation).sourceOuterAuthority ≠
        (successorStandingRenewal continuation).targetOuterAuthority ∧
      (successorStandingRenewal continuation).sourceActualServiceK ≠
        (successorStandingRenewal continuation).targetActualServiceK ∧
      (∀ channel : EssentialAccessChannel,
        Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1 + 1) channel)) ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (paidContinuationStep continuation).targetCurrent.actualExit) := by
  have future := successorRoleIndependentFutureExact continuation
  have external :=
    successorExternalConsumerSuccessorAndFurtherNext continuation
  exact
    ⟨executedPaidNext_isSuccessorOuterOccurrence continuation,
      successorAction_eq_executedAction continuation,
      future.1, future.2.2.1,
      ⟨successorActionableExit continuation⟩,
      future.2.2.2.2.1,
      future.2.2.2.2.2.2,
      executedAndSuccessorOuterAuthorities_distinct continuation,
      executedAndSuccessorActualServiceK_distinct continuation,
      fun channel => (everySuccessorChannelServiceAndNext continuation channel).1,
      external.2.1⟩

end SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt

/-! ## Full-capture countermodel preserving the bare future -/

structure ExactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (positive :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) : Type 31 where
  bareFuture : birthBearerExitRelationCompiler.FutureContinuationAt
    birthBearerIndependentExitRelation.1 .target
      positive.successorContinuationAction.1
  bareFutureWitness :
    birthBearerExitRelationCompiler.FutureContinuationWitnessAt
      birthBearerIndependentExitRelation.1 .target
        positive.successorContinuationAction.1 bareFuture
  relationLevelActionable : ActionableAt
    birthBearerExitRelationCompiler.futureIdle
    (birthBearerExitRelationCompiler.futureCodesAt
      birthBearerIndependentExitRelation .target)
    positive.successorContinuationAction.1
  sameActionCaptured : birthBearerFullCapture.Captures
    positive.successorContinuationAction.1
  capturedActionabilityEmpty :
    IsEmpty BirthBearerFullCaptureActionableExit
  installedPaymentAxisExact :
    birthBearerCapturedProgram.purchasingPowerStanding =
      birthBearerExitCapacityProgram.purchasingPowerStanding
  installedEmploymentAxisExact :
    birthBearerCapturedProgram.employmentLoss =
      birthBearerExitCapacityProgram.employmentLoss
  installedExitInterestAxisExact :
    birthBearerCapturedProgram.exitInterest =
      birthBearerExitCapacityProgram.exitInterest

def exactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ExactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
        oldVisit sourceIndex index) := by
  let positive :=
    sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index
  have actionFromRoot :=
    positive.successorPayment.continuationActionFromRootRead
  exact
    { bareFuture := by
        change birthBearerExitRelationCompiler.FutureContinuationAt
          birthBearerIndependentExitRelation.1 .target
            positive.successorPayment.continuationAction.1
        rw [actionFromRoot]
        exact positive.successorContinuationCarrier.futureContinuation
      bareFutureWitness := by
        exact birthBearerExitRelationCompiler.futureContinuation_witnessed
          birthBearerIndependentExitRelation.1 .target
            positive.successorPayment.continuationAction.1 _
      relationLevelActionable := by
        rw [positive.successorContinuationAction_eq_canonical]
        exact birthBearerLeave_target_actionable
      sameActionCaptured := by
        rw [positive.successorContinuationAction_eq_canonical]
        rfl
      capturedActionabilityEmpty :=
        birthBearerFullCaptureActionableExit_isEmpty
      installedPaymentAxisExact := rfl
      installedEmploymentAxisExact := rfl
      installedExitInterestAxisExact := rfl }

structure ExactPaidSuccessorFullCaptureReportedActionableContinuationAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (positive :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) : Type 32 where
  countermodel :
    ExactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
      positive
  falseActionableExit : BirthBearerFullCaptureActionableExit

theorem fullCaptureReportedActionableContinuation_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (positive :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :
    IsEmpty
      (ExactPaidSuccessorFullCaptureReportedActionableContinuationAt
        positive) :=
  ⟨fun falseReport =>
    falseReport.countermodel.capturedActionabilityEmpty.false
      falseReport.falseActionableExit⟩

theorem paidSuccessorBearerRoleIndependentContinuation_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let continuation :=
    sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index
  fail_if_success exact continuation.payment
  fail_if_success exact continuation.action
  fail_if_success exact continuation.successor
  fail_if_success exact continuation.target
  fail_if_success exact continuation.occurrence
  fail_if_success exact continuation.capture
  fail_if_success exact continuation.registry
  fail_if_success exact continuation.future
  trivial

end
end M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation.sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation.SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt.paidSuccessorBearerRoleIndependentContinuation_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation.exactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation.fullCaptureReportedActionableContinuation_isEmpty
