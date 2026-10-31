import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Disposition.Producer.SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition

/-!
# Root-temporal spine of the paid-exit lifecycle

This file defines the independent, occurrence-indexed authority contract used
by the maximum paid-exit lifecycle.  It introduces no lifecycle occurrence or
history object.  All stages are projections of the existing canonical final
disposition and its three Payment-generated successor edges.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidExitLifecycleTemporalSpine

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
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityBearerLeaveExecution
open M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open M14SourceGeneratedPaidSuccessorBearerLeaveExecution
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition

def paidExitLifecycleStandingRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex index

def paidExitLifecycleAntiRetaliationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
    sourceIndex index

def paidExitLifecycleExecutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
    index

def paidExitLifecycleContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
    sourceIndex index

def paidExitLifecycleDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedPaidSuccessorPostContinuationExternalResidualDispositionAt
    oldVisit sourceIndex index

def paidExitLifecycleFurtherStandingRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex (index + 1 + 1)

def paidExitLifecycleFurtherPaidStepAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  (paidExitLifecycleDispositionAt oldVisit sourceIndex index).furtherPaidStep

def paidExitLifecycleSuccessorDepthAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Nat :=
  contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
    (index + 1 + 1)

abbrev PaidExitLifecycleStage := Fin 4

def paidExitLifecycleStageRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (stage : PaidExitLifecycleStage) :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex (index + stage.1)

def paidExitLifecycleAuthorityCurrentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (stage : PaidExitLifecycleStage) : Nat :=
  (paidExitLifecycleStageRenewalAt oldVisit sourceIndex index stage
    ).sourceAuthorityCurrent

def paidExitLifecycleOuterAuthorityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (stage : PaidExitLifecycleStage) :=
  (paidExitLifecycleStageRenewalAt oldVisit sourceIndex index stage
    ).sourceOuterAuthority

def paidExitLifecycleActualServiceKAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (stage : PaidExitLifecycleStage) :=
  (paidExitLifecycleStageRenewalAt oldVisit sourceIndex index stage
    ).sourceActualServiceK

def paidExitLifecycleActionReadoutAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (stage : PaidExitLifecycleStage) :=
  (paidExitLifecycleStageRenewalAt oldVisit sourceIndex index stage
    ).sourceConsequence.exerciseAction

theorem paidExitLifecycleAuthorityCurrentAt_injective
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Function.Injective
      (paidExitLifecycleAuthorityCurrentAt oldVisit sourceIndex index) := by
  intro left right equality
  apply Fin.ext
  change
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (index + left.1) =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (index + right.1) at equality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at equality
  omega

theorem paidExitLifecycleOuterAuthorityAt_injective
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Function.Injective
      (paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index) := by
  intro left right equality
  apply paidExitLifecycleAuthorityCurrentAt_injective oldVisit sourceIndex index
  exact congrArg Sigma.fst equality

theorem paidExitLifecycleActualServiceKAt_injective
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Function.Injective
      (paidExitLifecycleActualServiceKAt oldVisit sourceIndex index) := by
  intro left right equality
  apply paidExitLifecycleAuthorityCurrentAt_injective oldVisit sourceIndex index
  exact
    contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt_injective
      oldVisit sourceIndex equality

theorem paidExitLifecycleActionReadoutAt_eq_canonical
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (stage : PaidExitLifecycleStage) :
    paidExitLifecycleActionReadoutAt oldVisit sourceIndex index stage =
      birthBearerExactExitExerciseAction :=
  (paidExitLifecycleStageRenewalAt oldVisit sourceIndex index stage
    ).sourceAction_eq_canonical

theorem paidExitLifecycleSameActionReadout_differentAuthorityAndK
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (left right : PaidExitLifecycleStage) (distinct : left ≠ right) :
    paidExitLifecycleActionReadoutAt oldVisit sourceIndex index left =
        paidExitLifecycleActionReadoutAt oldVisit sourceIndex index right ∧
      paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index left ≠
        paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index right ∧
      paidExitLifecycleActualServiceKAt oldVisit sourceIndex index left ≠
        paidExitLifecycleActualServiceKAt oldVisit sourceIndex index right :=
  ⟨(paidExitLifecycleActionReadoutAt_eq_canonical oldVisit sourceIndex index
      left).trans
      (paidExitLifecycleActionReadoutAt_eq_canonical oldVisit sourceIndex index
        right).symm,
    fun equality => distinct
      (paidExitLifecycleOuterAuthorityAt_injective oldVisit sourceIndex index
        equality),
    fun equality => distinct
      (paidExitLifecycleActualServiceKAt_injective oldVisit sourceIndex index
        equality)⟩

structure PaidExitLifecycleOccurrenceSpineAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop where
  firstPaidNext :
    HEq
      (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
        ).sourcePayment.nextPaidBy
      (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
        ).targetConsequence.outerRootEvent.occurrence
  secondPaidNext :
    HEq
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).executedPayment.nextPaidBy
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorRootEvent.occurrence
  thirdPaidNext :
    HEq
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorPayment.nextPaidBy
      (paidExitLifecycleFurtherPaidStepAt oldVisit sourceIndex index
        ).targetRootEvent.occurrence
  paymentChainExact :
    (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
        ).targetPayment =
          (paidExitLifecycleContinuationAt oldVisit sourceIndex index
            ).executedPayment ∧
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorStandingRenewal.sourcePayment =
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).executedPayment ∧
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorStandingRenewal.targetPayment =
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorPayment ∧
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
          ).sourcePayment =
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorPayment ∧
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
          ).targetPayment =
        (paidExitLifecycleFurtherPaidStepAt oldVisit sourceIndex index
          ).targetPayment ∧
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
          ).targetConsequence.outerRootEvent =
        (paidExitLifecycleFurtherPaidStepAt oldVisit sourceIndex index
          ).targetRootEvent

theorem paidExitLifecycleOccurrenceSpineAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidExitLifecycleOccurrenceSpineAt oldVisit sourceIndex index := by
  let renewal := paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
  let continuation :=
    paidExitLifecycleContinuationAt oldVisit sourceIndex index
  let disposition := paidExitLifecycleDispositionAt oldVisit sourceIndex index
  exact
    { firstPaidNext := renewal.sourcePaidNext_isTargetOuterOccurrence
      secondPaidNext := continuation.executedPaidNext_isSuccessorOuterOccurrence
      thirdPaidNext := disposition.furtherPaidNext_isExactOuterOccurrence
      paymentChainExact := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ }

structure PaidExitLifecycleResponseExecutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop where
  responseExecutionActionExact :
    (paidExitLifecycleExecutionAt oldVisit sourceIndex index
        ).targetExecutionAction =
      (paidExitLifecycleAntiRetaliationAt oldVisit sourceIndex index
        ).targetResponseAction
  actionCanonical :
    (paidExitLifecycleExecutionAt oldVisit sourceIndex index
        ).targetExecutionAction = birthBearerExactExitExerciseAction
  selfActionPowerExact :
    (paidExitLifecycleExecutionAt oldVisit sourceIndex index
        ).targetExecutionSelfActionPower.action =
      (paidExitLifecycleExecutionAt oldVisit sourceIndex index
        ).targetExecutionAction
  sourceRoleEmployed :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
      .source = .employed
  targetRoleReleased :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
      .target = .released
  lostWorkFuture :
    (paidExitLifecycleExecutionAt oldVisit sourceIndex index
        ).targetExecutionSelfActionPower.freedomChange =
      birthBearerEmploymentFreedomLoss
  installedNoncapture :
    ¬ birthBearerNoCapture.Captures
      (paidExitLifecycleExecutionAt oldVisit sourceIndex index
        ).targetExecutionAction.1
  terminateControllerSeparate : birthBearerEmployer ≠ birthBearerWorker

theorem paidExitLifecycleResponseExecutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidExitLifecycleResponseExecutionAt oldVisit sourceIndex index := by
  let execution := paidExitLifecycleExecutionAt oldVisit sourceIndex index
  have incidence := execution.targetOwnExecutionIncidence
  have power := execution.targetSelfActionPowerAndRelationExact
  have noncapture := execution.installedNoncaptureAndCapacityRemain
  have terminate := execution.realTerminateAuthorityRemainsSeparate
  exact
    { responseExecutionActionExact := incidence.2.2.2.1
      actionCanonical := execution.targetExecutionAction_eq_canonical
      selfActionPowerExact := power.1
      sourceRoleEmployed := power.2.2.2.2.1
      targetRoleReleased := power.2.2.2.2.2.1
      lostWorkFuture := power.2.2.2.2.2.2.1
      installedNoncapture := noncapture.1
      terminateControllerSeparate := terminate.2.2.2.1 }

structure PaidExitLifecycleRoleIndependentContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (code : ExitFutureCode) : Prop where
  codeExact : code =
    (paidExitLifecycleContinuationAt oldVisit sourceIndex index
      ).successorContinuationAction.1
  actionEqualsExecution :
    (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction =
      (paidExitLifecycleExecutionAt oldVisit sourceIndex index
        ).targetExecutionAction
  phaseZero :
    birthBearerExitRelationCompiler.phaseStep
      birthBearerIndependentExitRelation = 0
  sourceRoleIndependent :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
      .source = .independent
  targetRoleIndependent :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
      .target = .independent
  witnessedFuture :
    ∃ future : birthBearerExitRelationCompiler.FutureContinuationAt
        birthBearerIndependentExitRelation.1 .target code,
      birthBearerExitRelationCompiler.FutureContinuationWitnessAt
        birthBearerIndependentExitRelation.1 .target code future
  installedActionableExit : Nonempty BirthBearerRoleIndependentActionableExit
  installedNoncapture : ¬ birthBearerNoCapture.Captures code
  falseIndependentExecutionEmpty :
    IsEmpty BirthBearerIndependentExitFalseExecutionPower

theorem paidExitLifecycleRoleIndependentContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidExitLifecycleRoleIndependentContinuationAt oldVisit sourceIndex index
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction.1 := by
  let continuation :=
    paidExitLifecycleContinuationAt oldVisit sourceIndex index
  have future := continuation.successorRoleIndependentFutureExact
  exact
    { codeExact := rfl
      actionEqualsExecution := continuation.successorAction_eq_executedAction
      phaseZero := future.1
      sourceRoleIndependent := future.2.1
      targetRoleIndependent := future.2.2.1
      witnessedFuture := future.2.2.2.2.1
      installedActionableExit := ⟨continuation.successorActionableExit⟩
      installedNoncapture := future.2.2.2.2.2.1
      falseIndependentExecutionEmpty := future.2.2.2.2.2.2 }

structure PaidExitLifecycleExternalDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop where
  compilerWriteExact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorRootEvent.occurrence =
      .nativeWrite
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorPayment.write
  actualExitFromWrite :
    (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).paidContinuationStep.targetCurrent.actualExit =
      Classical.choice
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorPayment.write.down
  sourceOwnedResidual :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership
  rootConsumer : Nonempty
    (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).paidContinuationStep.targetCurrent.actualExit)
  exactSettlement : Nonempty
    { settlement : ExactServedCrossingDebitedRunAt
        (anomiePhaseAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index))
        debited
        (serviceCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)) //
      settlement =
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).paidContinuationStep.targetCurrent.actualExit.actualSettlement }
  rootFactorization :
    (paidExitLifecycleContinuationAt oldVisit sourceIndex index
      ).paidContinuationStep.targetCurrent.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes
  localLedgerEmpty : IsEmpty
    (OpenResponsibilityAt (JointSettlementNAt oldVisit)
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorRootEvent.occurrence.1)
  localDispositionTotal : Nonempty
    ((entry : OpenResponsibilityAt (JointSettlementNAt oldVisit)
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorRootEvent.occurrence.1) →
      LedgerEntryDispositionAt (JointSettlementNAt oldVisit) entry)
  substantiveLocalDispositionEmpty : IsEmpty
    (PostContinuationLocalDispositionWitnessAt
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index))
  externalLiabilityNonempty : Nonempty
    (PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
      (index + 1 + 1)
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorRootEvent
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).paidContinuationStep.targetCurrent.actualExit)
  exactNoErasure :
    ¬ (IsEmpty
          (OpenResponsibilityAt (JointSettlementNAt oldVisit)
            (paidExitLifecycleContinuationAt oldVisit sourceIndex index
              ).successorRootEvent.occurrence.1) →
        ¬ PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
          (index + 1 + 1)
          (paidExitLifecycleContinuationAt oldVisit sourceIndex index
            ).successorRootEvent
          (paidExitLifecycleContinuationAt oldVisit sourceIndex index
            ).paidContinuationStep.targetCurrent.actualExit)

theorem paidExitLifecycleExternalDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex index := by
  let continuation :=
    paidExitLifecycleContinuationAt oldVisit sourceIndex index
  let disposition := paidExitLifecycleDispositionAt oldVisit sourceIndex index
  have localExternal :=
    disposition.substantiveLocalDispositionEmpty_externalLiabilityNonempty
  exact
    { compilerWriteExact :=
        PostContinuationExternalResidualDispositionAt.successorCompilerWriteExact
          (continuation := continuation)
      actualExitFromWrite :=
        PostContinuationExternalResidualDispositionAt.successorActualExitFromWriteExact
          (continuation := continuation)
      sourceOwnedResidual := disposition.sourceOwnedResidual
      rootConsumer := disposition.rootConsumer
      exactSettlement := disposition.exactSettlement
      rootFactorization := disposition.rootFactorization
      localLedgerEmpty := disposition.localLedgerEmpty
      localDispositionTotal := ⟨disposition.localDisposition⟩
      substantiveLocalDispositionEmpty := localExternal.1
      externalLiabilityNonempty := localExternal.2
      exactNoErasure := disposition.localEmpty_doesNotEraseExactExternalLiability }

structure PaidExitLifecycleServicesAndFutureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop where
  executionServices : ∀ channel : EssentialAccessChannel,
    Nonempty
      (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex (index + 1) channel)
  continuationServices : ∀ channel : EssentialAccessChannel,
    Nonempty
      (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex (index + 1 + 1) channel)
  furtherServices : ∀ channel : EssentialAccessChannel,
    Nonempty
      (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
        sourceIndex (index + 1 + 1 + 1) channel)
  wholeLedgerSuccessorExact :
    (paidExitLifecycleDispositionAt oldVisit sourceIndex index
        ).wholeLedgerSuccessor =
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorPayment.successor
  furtherExternalConsumer : Nonempty
    (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
        ).targetConsequence.actualExit)
  furtherWholeLedgerSuccessor :
    HEq
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
        ).targetConsequence.successor
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
        ).targetPayment.successor
  furtherPaymentContinues :
    (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
        ).targetPayment.nextPaidBy =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        ((paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
          ).targetAuthorityCurrent + 1)

theorem paidExitLifecycleServicesAndFutureAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex index := by
  let execution := paidExitLifecycleExecutionAt oldVisit sourceIndex index
  let continuation :=
    paidExitLifecycleContinuationAt oldVisit sourceIndex index
  let disposition := paidExitLifecycleDispositionAt oldVisit sourceIndex index
  let further :=
    paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
  exact
    { executionServices := fun channel =>
        (execution.everyTargetChannelServiceAndNextRemain channel).1
      continuationServices := fun channel =>
        (continuation.everySuccessorChannelServiceAndNext channel).1
      furtherServices := fun channel =>
        ⟨(further.paidStep).targetChannel channel⟩
      wholeLedgerSuccessorExact := disposition.wholeLedgerSuccessorExact
      furtherExternalConsumer :=
        further.sourceAndTargetExternalConsumers.2.2
      furtherWholeLedgerSuccessor := further.targetPaymentContinues.2.2.1
      furtherPaymentContinues := further.targetPaymentContinues.2.2.2 }

/-- Independent authority contract for the exact code selected by the
actionable-renewal mouth. -/
structure PaidExitLifecycleRootTemporalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (code : ExitFutureCode) : Prop where
  occurrenceSpine :
    PaidExitLifecycleOccurrenceSpineAt oldVisit sourceIndex index
  responseExecution :
    PaidExitLifecycleResponseExecutionAt oldVisit sourceIndex index
  roleIndependentContinuation :
    PaidExitLifecycleRoleIndependentContinuationAt oldVisit sourceIndex index
      code
  externalDisposition :
    PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex index
  servicesAndFuture :
    PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex index
  outerAuthorityInjective : Function.Injective
    (paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index)
  actualServiceKInjective : Function.Injective
    (paidExitLifecycleActualServiceKAt oldVisit sourceIndex index)
  actionReadoutConstant : ∀ stage : PaidExitLifecycleStage,
    paidExitLifecycleActionReadoutAt oldVisit sourceIndex index stage =
      birthBearerExactExitExerciseAction

theorem paidExitLifecycleRootTemporalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidExitLifecycleRootTemporalAt oldVisit sourceIndex index
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction.1 where
  occurrenceSpine := paidExitLifecycleOccurrenceSpineAt oldVisit sourceIndex
    index
  responseExecution := paidExitLifecycleResponseExecutionAt oldVisit
    sourceIndex index
  roleIndependentContinuation :=
    paidExitLifecycleRoleIndependentContinuationAt oldVisit sourceIndex index
  externalDisposition := paidExitLifecycleExternalDispositionAt oldVisit
    sourceIndex index
  servicesAndFuture := paidExitLifecycleServicesAndFutureAt oldVisit
    sourceIndex index
  outerAuthorityInjective :=
    paidExitLifecycleOuterAuthorityAt_injective oldVisit sourceIndex index
  actualServiceKInjective :=
    paidExitLifecycleActualServiceKAt_injective oldVisit sourceIndex index
  actionReadoutConstant :=
    paidExitLifecycleActionReadoutAt_eq_canonical oldVisit sourceIndex index

theorem paidExitLifecycleRootTemporal_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let rooted := paidExitLifecycleRootTemporalAt oldVisit sourceIndex index
  fail_if_success exact rooted.payment
  fail_if_success exact rooted.action
  fail_if_success exact rooted.consumer
  fail_if_success exact rooted.capture
  fail_if_success exact rooted.registry
  fail_if_success exact rooted.future
  trivial

end
end M14SourceGeneratedPaidExitLifecycleTemporalSpine
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidExitLifecycleTemporalSpine.paidExitLifecycleRootTemporalAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidExitLifecycleTemporalSpine.paidExitLifecycleSameActionReadout_differentAuthorityAndK
