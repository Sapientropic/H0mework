import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Refusal.Producer.SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation

/-!
# Paid-successor exact bearer leave execution

The paid successor's existing post-settlement root owns a
`.bearerLeaveExecution` dependent face.  Its own Payment reads from that face
the exact `.t1/.leave` self-action power over the phase-one employment
relation.  The generated relation fold releases the worker and the common
employment future fibre loses `.work`.

This is exact structural execution authority.  It does not claim that the
action caused the already generated Payment, whole-ledger successor or paid
next.  Those authorities remain independently live.  The real
`.t0/.terminate` employment power remains separately source witnessed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidSuccessorBearerLeaveExecution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
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
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation

/-- Zero-payload cross-current execution certificate. -/
inductive SourceGeneratedPaidSuccessorBearerLeaveExecutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 29
  | private sealed

def sourceGeneratedPaidSuccessorBearerLeaveExecutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
      index :=
  .sealed

namespace SourceGeneratedPaidSuccessorBearerLeaveExecutionAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
    sourceIndex index)

include execution

theorem eq_sealed :
    execution = sourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index := by
  cases execution
  rfl

def antiRetaliation
    (_execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index :=
  sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
    sourceIndex index

def standingRenewal
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (antiRetaliation certificate).standingRenewal

def sourcePayment
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (antiRetaliation certificate).sourcePayment

def targetConsequence
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (antiRetaliation certificate).targetConsequence

def targetPayment
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (antiRetaliation certificate).targetPayment

def targetExecutionFace
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (targetPayment certificate).executionFace

def targetExecutionRootRead
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (targetPayment certificate).executionRootRead

def targetExecutionCarrier
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (targetPayment certificate).executionCarrier

def targetExecutionAction
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (targetPayment certificate).executionAction

def targetExecutionSelfActionPower
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  (targetPayment certificate).executionSelfActionPower

def targetChannel
    (certificate : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index)
    (channel : EssentialAccessChannel) :=
  ((antiRetaliation certificate).standingRenewal.paidStep).targetChannel channel

/-- The target Payment itself reads the execution carrier from its own root
face; response and execution actions are the same exact action seed. -/
theorem targetOwnExecutionIncidence :
    (targetExecutionFace execution).projection =
        ContributionCapacityPostSettlementRenewalProjection.bearerLeaveExecution ∧
      targetExecutionCarrier execution =
        Classical.choice (targetExecutionRootRead execution).down ∧
      targetExecutionAction execution =
        (targetExecutionCarrier execution).exerciseActionValue ∧
      targetExecutionAction execution =
        (antiRetaliation execution).targetResponseAction ∧
      targetExecutionSelfActionPower execution =
        (targetExecutionCarrier execution).selfActionPower ∧
      (targetExecutionSelfActionPower execution).action =
        targetExecutionAction execution :=
  let incidence := (targetPayment execution).bearerLeaveExecution_exact
  ⟨incidence.1, incidence.2.1, incidence.2.2.1,
    incidence.2.2.2.1, incidence.2.2.2.2.1,
    incidence.2.2.2.2.2.1⟩

theorem targetExecutionAction_eq_canonical :
    targetExecutionAction execution =
      birthBearerExactExitExerciseAction :=
  (targetPayment execution).executionAction_eq_responseAction.trans
    (antiRetaliation execution).targetResponseAction_eq_canonical

/-- Exact self-controller, generated interest, nonzero phase, role release and
future-fibre change.  The final conjunct classifies every possible generated
relation for this self-action controller, not only the two named negatives. -/
theorem targetSelfActionPowerAndRelationExact :
    (targetExecutionSelfActionPower execution).action =
        targetExecutionAction execution ∧
      birthBearerExitExerciseController.ControllerAt
        (targetExecutionAction execution) birthBearerWorker ∧
      birthBearerExitRelationCompiler.GeneratedInterestAt
        birthBearerWorker birthBearerEmploymentRelation ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerEmploymentRelation ≠ 0 ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .source = .employed ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .target = .released ∧
      (targetExecutionSelfActionPower execution).freedomChange =
        birthBearerEmploymentFreedomLoss ∧
      birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .source ≠
        birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .target ∧
      (∀ relation : birthBearerExitRelationCompiler.GeneratedRelation,
        ActionPowerOverAt birthBearerExitRelationCompiler
            birthBearerExitExerciseController birthBearerWorker
              birthBearerWorker relation →
          relation = birthBearerEmploymentRelation) := by
  have powerFromRoot :=
    (targetPayment execution).executionSelfActionPowerFromRootRead
  have carrier := targetExecutionCarrier execution
  exact
    ⟨(targetPayment execution).executionPowerActionExact,
      (by
        change birthBearerExitExerciseController.ControllerAt
          (targetPayment execution).executionAction birthBearerWorker
        rw [(targetPayment execution).executionActionFromRootRead]
        exact carrier.controllerExact),
      carrier.employmentInterestExact,
      carrier.employmentPhaseNonzero,
      (targetPayment execution).executionSourceRoleExact,
      (targetPayment execution).executionTargetRoleExact,
      (by
        change (targetPayment execution).executionSelfActionPower.freedomChange =
          birthBearerEmploymentFreedomLoss
        rw [powerFromRoot]
        exact (targetPayment execution).executionCarrier.freedomChangeExact),
      (targetExecutionSelfActionPower execution).freedom_ne,
      fun relation power =>
        birthBearerSelfActionPower_relation_eq_employment relation power⟩

theorem targetExecutionActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          (targetExecutionAction execution).1 := by
  rcases (targetExecutionCarrier execution).actionControllerSourceTrace with
    ⟨state, inTrace, stateExact, admitted⟩
  exact ⟨state, inTrace, stateExact, by
    change birthBearerExitExerciseController.actionAdmittedAt
      (targetPayment execution).executionAction.1
    rw [(targetPayment execution).executionActionFromRootRead]
    exact admitted⟩

theorem targetEmploymentRelationSourceTrace :
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
        birthBearerEmploymentRelation :=
  (targetExecutionCarrier execution).employmentRelationSourceTrace

/-- The `.t0/.terminate` action remains a distinct real authority, rather
than being overwritten by the `.t1/.leave` self-action. -/
theorem realTerminateAuthorityRemainsSeparate :
    (antiRetaliation execution).targetResponseCarrier.employmentLoss =
        birthBearerEmploymentLoss ∧
      (antiRetaliation execution).targetResponseCarrier.employmentLoss.power.action =
        birthBearerExactEmploymentAction ∧
      birthBearerEmploymentController.ControllerAt
        (antiRetaliation execution).targetResponseCarrier.employmentLoss.power.action
          birthBearerEmployer ∧
      birthBearerEmployer ≠ birthBearerWorker ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = birthBearerEmploymentController.actionState
            Lifecycle.actualEventGame.source ∧
          birthBearerEmploymentController.actionAdmittedAt
            (antiRetaliation execution).targetResponseCarrier.employmentLoss.power.action.1) := by
  have authority :=
    (antiRetaliation execution).realEmploymentLossAndControllerRemain
  exact ⟨authority.1, authority.2.1, authority.2.2.1,
    authority.2.2.2,
    (antiRetaliation execution).realEmploymentActionSourceTrace⟩

theorem outerAuthorityAndActualServiceKRemainDistinct :
    (standingRenewal execution).sourceOuterAuthority ≠
        (standingRenewal execution).targetOuterAuthority ∧
      (standingRenewal execution).sourceActualServiceK ≠
        (standingRenewal execution).targetActualServiceK :=
  ⟨(antiRetaliation execution).sourceAndTargetOuterAuthorities_distinct,
    (antiRetaliation execution).sourceAndTargetActualServiceK_distinct⟩

theorem installedNoncaptureAndCapacityRemain :
    (¬ birthBearerNoCapture.Captures
        (targetExecutionAction execution).1) ∧
      (birthBearerGeometryCompilerAt
        (standingRenewal execution).targetAuthorityCurrent
        ).actionableExitCapacity = 1 := by
  change (¬ birthBearerNoCapture.Captures
      (targetPayment execution).executionAction.1) ∧ _
  rw [(targetPayment execution).executionAction_eq_responseAction]
  exact ⟨(targetPayment execution).responseActionUncaptured,
    (targetPayment execution).responseExactCapacity⟩

theorem everyTargetChannelServiceAndNextRemain :
    ∀ channel : EssentialAccessChannel,
      let consumed := targetChannel execution channel
      Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1) channel) ∧
        consumed.2.actualNext = (targetPayment execution).nextPaidBy :=
  (antiRetaliation execution).everyTargetChannelServiceAndNext

theorem externalConsumerSuccessorAndPaidNextRemain :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (targetConsequence execution).actualExit) ∧
      HEq (targetConsequence execution).successor
        (targetPayment execution).successor ∧
      (targetPayment execution).nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          ((standingRenewal execution).targetAuthorityCurrent + 1) :=
  (antiRetaliation execution).targetExternalConsumerSuccessorAndNextRemain

/-- Main paid-successor exact execution seal.  Existing next authority is
retained, never reclassified as an effect caused by the leave action. -/
theorem paidSuccessorBearerLeaveExecution_exact :
    HEq (sourcePayment execution).nextPaidBy
        (targetConsequence execution).outerRootEvent.occurrence ∧
      targetExecutionAction execution =
        birthBearerExactExitExerciseAction ∧
      (targetExecutionSelfActionPower execution).action =
        targetExecutionAction execution ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .source = .employed ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .target = .released ∧
      (targetExecutionSelfActionPower execution).freedomChange =
        birthBearerEmploymentFreedomLoss ∧
      birthBearerEmployer ≠ birthBearerWorker ∧
      (¬ birthBearerNoCapture.Captures
        (targetExecutionAction execution).1) ∧
      (∀ channel : EssentialAccessChannel,
        Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1) channel)) ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (targetConsequence execution).actualExit) := by
  have selfPower := targetSelfActionPowerAndRelationExact execution
  have separate := realTerminateAuthorityRemainsSeparate execution
  have noncapture := installedNoncaptureAndCapacityRemain execution
  have external := externalConsumerSuccessorAndPaidNextRemain execution
  exact
    ⟨(antiRetaliation execution).sourcePaidNext_isTargetOuterOccurrence,
      targetExecutionAction_eq_canonical execution,
      selfPower.1, selfPower.2.2.2.2.1, selfPower.2.2.2.2.2.1,
      selfPower.2.2.2.2.2.2.1, separate.2.2.2.1,
      noncapture.1,
      fun channel =>
        ((antiRetaliation execution).targetChannelServiceAndNext channel).1,
      external.2.1⟩

end SourceGeneratedPaidSuccessorBearerLeaveExecutionAt

/-! ## Positive-preserving false relation retypings -/

/-- The entire positive target execution is retained while a second alleged
power changes a genuinely different generated relation. -/
structure ExactPaidSuccessorBearerLeaveFalseRelationExecutionAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index)
    (relation : birthBearerExitRelationCompiler.GeneratedRelation) : Type 30
    where
  positiveExecution : BirthBearerLeaveSelfActionPower
  positiveExecutionExact : positiveExecution =
    execution.targetExecutionSelfActionPower
  retypedExecution : ActionPowerOverAt birthBearerExitRelationCompiler
    birthBearerExitExerciseController birthBearerWorker birthBearerWorker
      relation
  relationDistinct : relation ≠ birthBearerEmploymentRelation

theorem falseRelationExecution_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index)
    (relation : birthBearerExitRelationCompiler.GeneratedRelation) :
    IsEmpty
      (ExactPaidSuccessorBearerLeaveFalseRelationExecutionAt execution
        relation) :=
  ⟨fun falseExecution =>
    falseExecution.relationDistinct
      (birthBearerSelfActionPower_relation_eq_employment relation
        falseExecution.retypedExecution)⟩

abbrev ExactPaidSuccessorIndependentExitFalseExecutionAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  ExactPaidSuccessorBearerLeaveFalseRelationExecutionAt execution
    birthBearerIndependentExitRelation

abbrev ExactPaidSuccessorNewJobFalseExecutionAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :=
  ExactPaidSuccessorBearerLeaveFalseRelationExecutionAt execution
    birthBearerNewJobRelation

theorem independentExitFalseExecution_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :
    IsEmpty (ExactPaidSuccessorIndependentExitFalseExecutionAt execution) :=
  falseRelationExecution_isEmpty execution birthBearerIndependentExitRelation

theorem newJobFalseExecution_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (execution : SourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit
      sourceIndex index) :
    IsEmpty (ExactPaidSuccessorNewJobFalseExecutionAt execution) :=
  falseRelationExecution_isEmpty execution birthBearerNewJobRelation

theorem paidSuccessorBearerLeaveExecution_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let execution :=
    sourceGeneratedPaidSuccessorBearerLeaveExecutionAt oldVisit sourceIndex
      index
  fail_if_success exact execution.payment
  fail_if_success exact execution.action
  fail_if_success exact execution.response
  fail_if_success exact execution.relation
  fail_if_success exact execution.target
  fail_if_success exact execution.occurrence
  fail_if_success exact execution.registry
  fail_if_success exact execution.future
  trivial

end
end M14SourceGeneratedPaidSuccessorBearerLeaveExecution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerLeaveExecution.sourceGeneratedPaidSuccessorBearerLeaveExecutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerLeaveExecution.SourceGeneratedPaidSuccessorBearerLeaveExecutionAt.paidSuccessorBearerLeaveExecution_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerLeaveExecution.falseRelationExecution_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerLeaveExecution.independentExitFalseExecution_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerLeaveExecution.newJobFalseExecution_isEmpty
