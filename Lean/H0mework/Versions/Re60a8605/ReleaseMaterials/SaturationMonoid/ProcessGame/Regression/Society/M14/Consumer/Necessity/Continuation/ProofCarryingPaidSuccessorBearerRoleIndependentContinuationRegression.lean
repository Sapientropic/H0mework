import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Continuation.Producer.SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Execution.ProofCarryingPaidSuccessorBearerLeaveExecutionRegression

/-!
# Direct consumer of paid-successor role-independent continuation

The audit consumes the paid-step HEq from the executed Payment, the successor
Payment's own continuation root read, exact action-content alignment, the
phase-zero independent relation future and capture-adjusted actionable exit,
index+1→index+2 authority/K renewal, services, external responsibility and the
further paid next.

The full-capture countermodel retains the same successor-indexed bare future
and relation-level actionability while only the capture-adjusted exit fibre is
empty.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPaidSuccessorBearerRoleIndependentContinuationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerLeaveExecution
open M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPaidSuccessorBearerLeaveExecution
open M14ProofCarryingPaidSuccessorBearerLeaveExecutionRegression
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation

abbrev CanonicalPaidSuccessorBearerRoleIndependentContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
    sourceIndex index

def canonicalPaidSuccessorBearerRoleIndependentContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index :=
  sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
    sourceIndex index

structure PaidSuccessorBearerRoleIndependentContinuationAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (continuation :
      CanonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) : Prop where
  canonicalExact : continuation =
    canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index
  priorExecutionAudit : PaidSuccessorBearerLeaveExecutionAuditAt
    continuation.execution
  paidStepSourceAndSuccessorExact :
    continuation.paidContinuationStep.sourcePayment =
          continuation.executedPayment ∧
      HEq continuation.executedPayment.nextPaidBy
        continuation.successorRootEvent.occurrence
  successorOwnContinuation :
    continuation.successorContinuationFace.projection =
          ContributionCapacityPostSettlementRenewalProjection.bearerRoleIndependentContinuation ∧
      continuation.successorContinuationCarrier =
        Classical.choice continuation.successorContinuationRootRead.down ∧
      continuation.successorContinuationAction =
        continuation.successorContinuationCarrier.exerciseActionValue ∧
      continuation.successorContinuationAction =
        continuation.successorPayment.executionAction ∧
      continuation.successorActionableExit =
        continuation.successorContinuationCarrier.actionableExit ∧
      continuation.successorActionableExit.1 =
        continuation.successorContinuationAction.1
  exactActionAndRoleIndependentFuture :
    continuation.successorContinuationAction =
          continuation.execution.targetExecutionAction ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerIndependentExitRelation = 0 ∧
      birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
          .source = .independent ∧
      birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
          .target = .independent ∧
      continuation.successorActionableExit.1 =
        continuation.successorContinuationAction.1 ∧
      (∃ future : birthBearerExitRelationCompiler.FutureContinuationAt
          birthBearerIndependentExitRelation.1 .target
            continuation.successorContinuationAction.1,
        birthBearerExitRelationCompiler.FutureContinuationWitnessAt
          birthBearerIndependentExitRelation.1 .target
            continuation.successorContinuationAction.1 future) ∧
      (¬ birthBearerNoCapture.Captures
        continuation.successorContinuationAction.1) ∧
      IsEmpty BirthBearerIndependentExitFalseExecutionPower
  independentRelationSourceTrace :
    ∃ seed : birthBearerExitRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = Lifecycle.Universal.FixedAdapter.targetFace.state
            Lifecycle.actualEventGame.source ∧
        birthBearerExitRelationCompiler.relationSeedAt
            Lifecycle.actualEventGame.source state seed.1 ∧
        Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
          Lifecycle.actualEventGame.source state
            (birthBearerExitRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor birthBearerExitRelationCompiler = birthBearerWorker ∧
      birthBearerExitRelationCompiler.relationOf seed =
        birthBearerIndependentExitRelation
  targetFutureBoundarySourceTrace :
    birthBearerExitRelationCompiler.futureBoundaryState
        birthBearerIndependentExitRelation.1 .target ∈
      Lifecycle.actualEventGame.occurrence.trace
  successorPaymentAndSettlementExact :
    continuation.successorContinuationCarrier.existingPaymentOccurrence =
          continuation.paidContinuationStep.targetCurrent.actualExit.paymentOccurrence ∧
      continuation.successorContinuationCarrier.existingActualSettlement =
        continuation.paidContinuationStep.targetCurrent.actualExit.actualSettlement
  executedAndSuccessorAuthorityRenewal :
    continuation.successorStandingRenewal.sourcePayment =
          continuation.executedPayment ∧
      continuation.successorStandingRenewal.targetPayment =
          continuation.successorPayment ∧
      continuation.successorStandingRenewal.sourceOuterAuthority ≠
          continuation.successorStandingRenewal.targetOuterAuthority ∧
      continuation.successorStandingRenewal.sourceActualServiceK ≠
        continuation.successorStandingRenewal.targetActualServiceK
  successorInstalledCapacityOne :
    (birthBearerGeometryCompilerAt
      continuation.successorStandingRenewal.targetAuthorityCurrent
      ).actionableExitCapacity = 1
  successorLocalLedgerEmpty : IsEmpty
    (OpenResponsibilityAt
      (M14SourceGeneratedContributionCapacityJointSettlementWorld.JointSettlementNAt
        oldVisit)
      continuation.successorRootEvent.occurrence.1)
  everySuccessorChannelServiceAndNext :
    ∀ channel : EssentialAccessChannel,
      let consumed := continuation.successorChannel channel
      Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1 + 1) channel) ∧
        consumed.2.actualNext = continuation.successorPayment.nextPaidBy
  successorExternalConsumerSuccessorAndFurtherNext :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          continuation.paidContinuationStep.targetCurrent.actualExit) ∧
      Nonempty
        (SourceNativeLedgerGeneratedSuccessorAt
          continuation.successorRootEvent.occurrence
          continuation.successorRootEvent.wholeLedgerWriteBack) ∧
      continuation.successorPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
              sourceIndex (index + 1 + 1) +
            1)
  fullCaptureCountermodel : Nonempty
    (ExactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
      continuation)
  fullCapturePreservesBareFutureAndNoncaptureAxes :
    ∃ countermodel :
        ExactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
          continuation,
      Nonempty
          (birthBearerExitRelationCompiler.FutureContinuationAt
            birthBearerIndependentExitRelation.1 .target
              continuation.successorContinuationAction.1) ∧
        countermodel.relationLevelActionable =
          birthBearerLeave_target_actionable ∧
        birthBearerFullCapture.Captures
          continuation.successorContinuationAction.1 ∧
        IsEmpty BirthBearerFullCaptureActionableExit ∧
        birthBearerCapturedProgram.purchasingPowerStanding =
          birthBearerExitCapacityProgram.purchasingPowerStanding ∧
        birthBearerCapturedProgram.employmentLoss =
          birthBearerExitCapacityProgram.employmentLoss ∧
        birthBearerCapturedProgram.exitInterest =
          birthBearerExitCapacityProgram.exitInterest
  fullCaptureFalseActionabilityEmpty : IsEmpty
    (ExactPaidSuccessorFullCaptureReportedActionableContinuationAt
      continuation)

theorem paidSuccessorBearerRoleIndependentContinuationAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidSuccessorBearerRoleIndependentContinuationAuditAt
      (canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) := by
  let continuation :=
    canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index
  have priorAudit : PaidSuccessorBearerLeaveExecutionAuditAt
      continuation.execution := by
    exact paidSuccessorBearerLeaveExecutionAuditAt oldVisit sourceIndex index
  have future := continuation.successorRoleIndependentFutureExact
  let countermodel :=
    exactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
      oldVisit sourceIndex index
  exact
    { canonicalExact := rfl
      priorExecutionAudit := priorAudit
      paidStepSourceAndSuccessorExact :=
        ⟨continuation.paidContinuationStep_source_isExecutedPayment,
          continuation.executedPaidNext_isSuccessorOuterOccurrence⟩
      successorOwnContinuation :=
        continuation.successorOwnContinuationIncidence
      exactActionAndRoleIndependentFuture :=
        ⟨continuation.successorAction_eq_executedAction,
          future.1, future.2.1, future.2.2.1,
          future.2.2.2.1, future.2.2.2.2.1,
          future.2.2.2.2.2.1, future.2.2.2.2.2.2⟩
      independentRelationSourceTrace :=
        continuation.successorContinuationCarrier.independentRelationSourceTrace
      targetFutureBoundarySourceTrace :=
        SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt.targetFutureBoundary_mem_actualOccurrence
      successorPaymentAndSettlementExact :=
        ⟨continuation.successorPayment.continuationPaymentOccurrenceExact,
          continuation.successorPayment.continuationSettlementExact⟩
      executedAndSuccessorAuthorityRenewal :=
        ⟨continuation.successorStandingRenewalPaymentsExact.1,
          continuation.successorStandingRenewalPaymentsExact.2,
          continuation.executedAndSuccessorOuterAuthorities_distinct,
          continuation.executedAndSuccessorActualServiceK_distinct⟩
      successorInstalledCapacityOne :=
        continuation.successorInstalledCapacityOne
      successorLocalLedgerEmpty :=
        continuation.paidContinuationStep.targetLocalLedger_isEmpty
      everySuccessorChannelServiceAndNext :=
        continuation.everySuccessorChannelServiceAndNext
      successorExternalConsumerSuccessorAndFurtherNext :=
        continuation.successorExternalConsumerSuccessorAndFurtherNext
      fullCaptureCountermodel := ⟨countermodel⟩
      fullCapturePreservesBareFutureAndNoncaptureAxes :=
        ⟨countermodel, ⟨countermodel.bareFuture⟩,
          rfl, countermodel.sameActionCaptured,
          countermodel.capturedActionabilityEmpty,
          countermodel.installedPaymentAxisExact,
          countermodel.installedEmploymentAxisExact,
          countermodel.installedExitInterestAxisExact⟩
      fullCaptureFalseActionabilityEmpty :=
        fullCaptureReportedActionableContinuation_isEmpty continuation }

structure ProofCarryingPaidSuccessorBearerRoleIndependentContinuationCertificate :
    Prop where
  everyContinuation : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (CanonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    PaidSuccessorBearerRoleIndependentContinuationAuditAt
      (canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index)
  everyFullCaptureCountermodel :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      Nonempty
        (ExactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
          (canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
            sourceIndex index))
  everyFullCaptureFalseActionabilityEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPaidSuccessorFullCaptureReportedActionableContinuationAt
          (canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
            sourceIndex index))

theorem proofCarryingPaidSuccessorBearerRoleIndependentContinuationDirectConsumer :
    ProofCarryingPaidSuccessorBearerRoleIndependentContinuationCertificate where
  everyContinuation := fun oldVisit sourceIndex index =>
    ⟨canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index⟩
  everyAudit := paidSuccessorBearerRoleIndependentContinuationAuditAt
  everyFullCaptureCountermodel := fun oldVisit sourceIndex index =>
    ⟨exactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
      oldVisit sourceIndex index⟩
  everyFullCaptureFalseActionabilityEmpty :=
    fun oldVisit sourceIndex index =>
      fullCaptureReportedActionableContinuation_isEmpty
        (canonicalPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
          sourceIndex index)

end
end M14ProofCarryingPaidSuccessorBearerRoleIndependentContinuationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorBearerRoleIndependentContinuationRegression.paidSuccessorBearerRoleIndependentContinuationAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorBearerRoleIndependentContinuationRegression.proofCarryingPaidSuccessorBearerRoleIndependentContinuationDirectConsumer
