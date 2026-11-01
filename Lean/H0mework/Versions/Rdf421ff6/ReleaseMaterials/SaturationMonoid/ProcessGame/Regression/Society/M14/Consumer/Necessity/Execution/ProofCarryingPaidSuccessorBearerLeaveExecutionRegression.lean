import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Execution.Producer.SourceGeneratedPaidSuccessorBearerLeaveExecution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Refusal.ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression

/-!
# Direct consumer of paid-successor bearer leave execution

The audit consumes the target Payment's own execution face/root read, the
exact self-action and relation traces, complete relation classification, the
separate `.t0/.terminate` authority, installed noncapture, all essential
service channels, external responsibility, successor and paid next.

The negative keeps the entire positive execution and adds a purported power
over any distinct generated relation.  Complete grammar classification makes
that type empty, with named independent-exit and new-work specializations.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPaidSuccessorBearerLeaveExecutionRegression

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
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open M14ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression
open M14SourceGeneratedPaidSuccessorBearerLeaveExecution

abbrev CanonicalPaidSuccessorBearerLeaveExecutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
    index

def canonicalPaidSuccessorBearerLeaveExecutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index :=
  sourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
    index

structure PaidSuccessorBearerLeaveExecutionAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (execution : CanonicalPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) : Prop where
  canonicalExact : execution =
    canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index
  priorAntiRetaliationAudit :
    PaidSuccessorAfterRefusalAntiRetaliationAuditAt
      execution.antiRetaliation
  targetOwnExecution :
    execution.targetExecutionFace.projection =
          ContributionCapacityPostSettlementRenewalProjection.bearerLeaveExecution ∧
      execution.targetExecutionCarrier =
        Classical.choice execution.targetExecutionRootRead.down ∧
      execution.targetExecutionAction =
        execution.targetExecutionCarrier.exerciseActionValue ∧
      execution.targetExecutionAction =
        execution.antiRetaliation.targetResponseAction ∧
      execution.targetExecutionSelfActionPower =
        execution.targetExecutionCarrier.selfActionPower ∧
      execution.targetExecutionSelfActionPower.action =
        execution.targetExecutionAction
  exactActionPowerAndCompleteRelationClassification :
    execution.targetExecutionAction = birthBearerExactExitExerciseAction ∧
      execution.targetExecutionSelfActionPower.action =
        execution.targetExecutionAction ∧
      birthBearerExitExerciseController.ControllerAt
        execution.targetExecutionAction birthBearerWorker ∧
      birthBearerExitRelationCompiler.GeneratedInterestAt
        birthBearerWorker birthBearerEmploymentRelation ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerEmploymentRelation ≠ 0 ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .source = .employed ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .target = .released ∧
      execution.targetExecutionSelfActionPower.freedomChange =
        birthBearerEmploymentFreedomLoss ∧
      birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .source ≠
        birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .target ∧
      (∀ relation : birthBearerExitRelationCompiler.GeneratedRelation,
        ActionPowerOverAt birthBearerExitRelationCompiler
            birthBearerExitExerciseController birthBearerWorker
              birthBearerWorker relation →
          relation = birthBearerEmploymentRelation)
  actionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          execution.targetExecutionAction.1
  relationSourceTrace :
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
        birthBearerEmploymentRelation
  separateTerminateAuthorityAndTrace :
    execution.antiRetaliation.targetResponseCarrier.employmentLoss =
          birthBearerEmploymentLoss ∧
      execution.antiRetaliation.targetResponseCarrier.employmentLoss.power.action =
          birthBearerExactEmploymentAction ∧
      birthBearerEmploymentController.ControllerAt
        execution.antiRetaliation.targetResponseCarrier.employmentLoss.power.action
          birthBearerEmployer ∧
      birthBearerEmployer ≠ birthBearerWorker ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = birthBearerEmploymentController.actionState
            Lifecycle.actualEventGame.source ∧
          birthBearerEmploymentController.actionAdmittedAt
            execution.antiRetaliation.targetResponseCarrier.employmentLoss.power.action.1)
  outerAuthorityAndActualServiceKDistinct :
    execution.standingRenewal.sourceOuterAuthority ≠
          execution.standingRenewal.targetOuterAuthority ∧
      execution.standingRenewal.sourceActualServiceK ≠
        execution.standingRenewal.targetActualServiceK
  installedNoncaptureAndCapacity :
    (¬ birthBearerNoCapture.Captures
        execution.targetExecutionAction.1) ∧
      (birthBearerGeometryCompilerAt
        execution.standingRenewal.targetAuthorityCurrent
        ).actionableExitCapacity = 1
  everyTargetChannelServiceAndNext :
    ∀ channel : EssentialAccessChannel,
      let consumed := execution.targetChannel channel
      Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1) channel) ∧
        consumed.2.actualNext = execution.targetPayment.nextPaidBy
  externalConsumerSuccessorAndPaidNext :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          execution.targetConsequence.actualExit) ∧
      HEq execution.targetConsequence.successor
        execution.targetPayment.successor ∧
      execution.targetPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (execution.standingRenewal.targetAuthorityCurrent + 1)
  everyDistinctRelationRetypingEmpty :
    ∀ relation : birthBearerExitRelationCompiler.GeneratedRelation,
      relation ≠ birthBearerEmploymentRelation →
        IsEmpty
          (ExactPaidSuccessorBearerLeaveFalseRelationExecutionAt execution
            relation)
  independentExitRetypingEmpty :
    IsEmpty (ExactPaidSuccessorIndependentExitFalseExecutionAt execution)
  newJobRetypingEmpty :
    IsEmpty (ExactPaidSuccessorNewJobFalseExecutionAt execution)

theorem paidSuccessorBearerLeaveExecutionAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidSuccessorBearerLeaveExecutionAuditAt
      (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
        index) := by
  let execution :=
    canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index
  have priorAudit :
      PaidSuccessorAfterRefusalAntiRetaliationAuditAt
        execution.antiRetaliation := by
    exact paidSuccessorAfterRefusalAntiRetaliationAuditAt oldVisit sourceIndex
      index
  have selfPower := execution.targetSelfActionPowerAndRelationExact
  exact
    { canonicalExact := rfl
      priorAntiRetaliationAudit := priorAudit
      targetOwnExecution := execution.targetOwnExecutionIncidence
      exactActionPowerAndCompleteRelationClassification :=
        ⟨execution.targetExecutionAction_eq_canonical,
          selfPower.1, selfPower.2.1, selfPower.2.2.1,
          selfPower.2.2.2.1, selfPower.2.2.2.2.1,
          selfPower.2.2.2.2.2.1, selfPower.2.2.2.2.2.2.1,
          selfPower.2.2.2.2.2.2.2.1,
          selfPower.2.2.2.2.2.2.2.2⟩
      actionSourceTrace := execution.targetExecutionActionSourceTrace
      relationSourceTrace := execution.targetEmploymentRelationSourceTrace
      separateTerminateAuthorityAndTrace :=
        execution.realTerminateAuthorityRemainsSeparate
      outerAuthorityAndActualServiceKDistinct :=
        execution.outerAuthorityAndActualServiceKRemainDistinct
      installedNoncaptureAndCapacity :=
        execution.installedNoncaptureAndCapacityRemain
      everyTargetChannelServiceAndNext :=
        execution.everyTargetChannelServiceAndNextRemain
      externalConsumerSuccessorAndPaidNext :=
        execution.externalConsumerSuccessorAndPaidNextRemain
      everyDistinctRelationRetypingEmpty := fun relation _distinct =>
        falseRelationExecution_isEmpty execution relation
      independentExitRetypingEmpty :=
        independentExitFalseExecution_isEmpty execution
      newJobRetypingEmpty := newJobFalseExecution_isEmpty execution }

structure ProofCarryingPaidSuccessorBearerLeaveExecutionCertificate : Prop
    where
  everyExecution : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (CanonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    PaidSuccessorBearerLeaveExecutionAuditAt
      (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index)
  everyDistinctRelationRetypingEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      ∀ relation : birthBearerExitRelationCompiler.GeneratedRelation,
        relation ≠ birthBearerEmploymentRelation →
          IsEmpty
            (ExactPaidSuccessorBearerLeaveFalseRelationExecutionAt
              (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit
                sourceIndex index) relation)
  everyIndependentExitRetypingEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPaidSuccessorIndependentExitFalseExecutionAt
          (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
            index))
  everyNewJobRetypingEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPaidSuccessorNewJobFalseExecutionAt
          (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
            index))

theorem proofCarryingPaidSuccessorBearerLeaveExecutionDirectConsumer :
    ProofCarryingPaidSuccessorBearerLeaveExecutionCertificate where
  everyExecution := fun oldVisit sourceIndex index =>
    ⟨canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index⟩
  everyAudit := paidSuccessorBearerLeaveExecutionAuditAt
  everyDistinctRelationRetypingEmpty :=
    fun oldVisit sourceIndex index relation _distinct =>
      falseRelationExecution_isEmpty
        (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
          index) relation
  everyIndependentExitRetypingEmpty := fun oldVisit sourceIndex index =>
    independentExitFalseExecution_isEmpty
      (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index)
  everyNewJobRetypingEmpty := fun oldVisit sourceIndex index =>
    newJobFalseExecution_isEmpty
      (canonicalPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex index)

end
end M14ProofCarryingPaidSuccessorBearerLeaveExecutionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorBearerLeaveExecutionRegression.paidSuccessorBearerLeaveExecutionAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorBearerLeaveExecutionRegression.proofCarryingPaidSuccessorBearerLeaveExecutionDirectConsumer
