import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Response.Producer.SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse

/-!
# Source-generated bearer leave execution

The exact `.t1/.leave` response action becomes genuine self-action power only
on the generated employment relation, whose phase is nonzero.  Controller and
affected actor are the same generated `.t1` worker; the relation fold moves the
worker from `.employed` to `.released` and the witnessed actionable-freedom
change loses `.work`.

The two phase-zero relations remain future possibilities: independent exit
and new work.  Both are constructively rejected as present execution
relations; among the complete generated relation grammar, action power forces
the employment relation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityBearerLeaveExecution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse

theorem birthBearerEmploymentRelationPhase_nonzero :
    birthBearerExitRelationCompiler.phaseStep birthBearerEmploymentRelation ≠
      0 := by
  change (1 : Int) ≠ 0
  norm_num

@[simp] theorem birthBearerEmploymentRelation_sourceRole_exact :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
        .source = .employed :=
  rfl

@[simp] theorem birthBearerEmploymentRelation_targetRole_exact :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
        .target = .released :=
  rfl

abbrev BirthBearerLeaveSelfActionPower :=
  ActionPowerOverAt birthBearerExitRelationCompiler
    birthBearerExitExerciseController birthBearerWorker birthBearerWorker
      birthBearerEmploymentRelation

abbrev BirthBearerIndependentExitFalseExecutionPower :=
  ActionPowerOverAt birthBearerExitRelationCompiler
    birthBearerExitExerciseController birthBearerWorker birthBearerWorker
      birthBearerIndependentExitRelation

def birthBearerNewJobRelation :
    birthBearerExitRelationCompiler.GeneratedRelation :=
  birthBearerExitRelationCompiler.relationOf
    (birthBearerExactRelationSeed .newJob)

abbrev BirthBearerNewJobFalseExecutionPower :=
  ActionPowerOverAt birthBearerExitRelationCompiler
    birthBearerExitExerciseController birthBearerWorker birthBearerWorker
      birthBearerNewJobRelation

/-- The independent-exit relation has phase zero and cannot be retyped as the
relation changed by an actual power exercise. -/
theorem birthBearerIndependentExitFalseExecutionPower_isEmpty :
    IsEmpty BirthBearerIndependentExitFalseExecutionPower :=
  ⟨fun falsePower => by
    have phaseNonzero := falsePower.constraint.phase_nonzero
    change (0 : Int) ≠ 0 at phaseNonzero
    exact phaseNonzero rfl⟩

/-- Future new work also has phase zero: it is not the relation changed by
the present leave exercise. -/
theorem birthBearerNewJobFalseExecutionPower_isEmpty :
    IsEmpty BirthBearerNewJobFalseExecutionPower :=
  ⟨fun falsePower => by
    have phaseNonzero := falsePower.constraint.phase_nonzero
    change (0 : Int) ≠ 0 at phaseNonzero
    exact phaseNonzero rfl⟩

/-- Across the complete generated `ExitRelationSeed` grammar, any self-action
power at this controller is necessarily power over the employment relation.
The future independent-exit and new-work relations cannot impersonate the
present execution. -/
theorem birthBearerSelfActionPower_relation_eq_employment
    (relation : birthBearerExitRelationCompiler.GeneratedRelation)
    (power : ActionPowerOverAt birthBearerExitRelationCompiler
      birthBearerExitExerciseController birthBearerWorker birthBearerWorker
        relation) :
    relation = birthBearerEmploymentRelation := by
  apply Subtype.ext
  have phaseNonzero := power.constraint.phase_nonzero
  change (match relation.1 with
    | .employment => (1 : Int)
    | .independentExit => 0
    | .newJob => 0) ≠ 0 at phaseNonzero
  cases lineageEq : relation.1 with
  | employment => rfl
  | independentExit =>
      exfalso
      apply phaseNonzero
      simp [lineageEq]
  | newJob =>
      exfalso
      apply phaseNonzero
      simp [lineageEq]

/-- Action-indexed execution carrier at one existing actual-exit authority. -/
structure SourceGeneratedContributionCapacityBearerLeaveExecutionAt
    (depth : Nat)
    (existingActualExit : PeriodicActualServiceExitAt depth)
    (exerciseAction :
      birthBearerExitExerciseController.ExactActionSeed) : Type 18 where
  private mk ::
  response :
    SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit exerciseAction
  selfActionPower : BirthBearerLeaveSelfActionPower
  selfActionExact : selfActionPower.action = exerciseAction
  controllerExact :
    birthBearerExitExerciseController.ControllerAt exerciseAction
      birthBearerWorker
  employmentInterestExact :
    birthBearerExitRelationCompiler.GeneratedInterestAt
      birthBearerWorker birthBearerEmploymentRelation
  employmentPhaseNonzero :
    birthBearerExitRelationCompiler.phaseStep birthBearerEmploymentRelation ≠
      0
  freedomChangeExact : selfActionPower.freedomChange =
    birthBearerEmploymentFreedomLoss
  sourceRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
      .source = .employed
  targetRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
      .target = .released
  responseActionUncaptured :
    ¬ birthBearerNoCapture.Captures exerciseAction.1
  realEmploymentLoss : BirthBearerEmploymentLossAuthority
  realEmploymentLossExact : realEmploymentLoss = birthBearerEmploymentLoss
  distinctEmploymentController : birthBearerEmployer ≠ birthBearerWorker
  existingPaymentOccurrence : PeriodicSourceBackedPaymentAt depth
  existingPaymentOccurrenceExact : existingPaymentOccurrence =
    existingActualExit.paymentOccurrence
  existingActualSettlement : ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) debited (serviceCompilerAt depth)
  existingActualSettlementExact : existingActualSettlement =
    existingActualExit.actualSettlement

abbrev CanonicalContributionCapacityBearerLeaveExecutionAt
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :=
  SourceGeneratedContributionCapacityBearerLeaveExecutionAt depth
    existingActualExit
    (sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit).exerciseActionValue

def sourceGeneratedContributionCapacityBearerLeaveExecutionAt
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :
    CanonicalContributionCapacityBearerLeaveExecutionAt depth
      existingActualExit := by
  let response :=
    sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit
  let selfActionPower : BirthBearerLeaveSelfActionPower :=
    { action := response.exerciseActionValue
      controller_exact := response.exerciseControllerExact
      constraint :=
        ⟨birthBearerEmploymentInterest,
          birthBearerEmploymentRelationPhase_nonzero⟩
      freedomChange := birthBearerEmploymentFreedomLoss }
  exact
    { response := response
      selfActionPower := selfActionPower
      selfActionExact := rfl
      controllerExact := response.exerciseControllerExact
      employmentInterestExact := birthBearerEmploymentInterest
      employmentPhaseNonzero := birthBearerEmploymentRelationPhase_nonzero
      freedomChangeExact := rfl
      sourceRoleExact := birthBearerEmploymentRelation_sourceRole_exact
      targetRoleExact := birthBearerEmploymentRelation_targetRole_exact
      responseActionUncaptured := response.actionUncaptured
      realEmploymentLoss := birthBearerEmploymentLoss
      realEmploymentLossExact := rfl
      distinctEmploymentController :=
        birthBearerEmployer_ne_birthBearerWorker
      existingPaymentOccurrence := response.existingPaymentOccurrence
      existingPaymentOccurrenceExact :=
        response.existingPaymentOccurrenceExact
      existingActualSettlement := response.existingActualSettlement
      existingActualSettlementExact :=
        response.existingActualSettlementExact }

namespace SourceGeneratedContributionCapacityBearerLeaveExecutionAt

variable {depth : Nat} {existingActualExit : PeriodicActualServiceExitAt depth}
  {exerciseAction : birthBearerExitExerciseController.ExactActionSeed}
  (execution : SourceGeneratedContributionCapacityBearerLeaveExecutionAt
    depth existingActualExit exerciseAction)

include execution

def exerciseActionValue
    (_execution : SourceGeneratedContributionCapacityBearerLeaveExecutionAt
      depth existingActualExit exerciseAction) :
    birthBearerExitExerciseController.ExactActionSeed :=
  exerciseAction

theorem exactSelfActionPower :
    execution.selfActionPower.action = execution.exerciseActionValue ∧
      birthBearerExitExerciseController.ControllerAt
        execution.exerciseActionValue birthBearerWorker ∧
      birthBearerExitRelationCompiler.GeneratedInterestAt
        birthBearerWorker birthBearerEmploymentRelation ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerEmploymentRelation ≠ 0 ∧
      execution.selfActionPower.freedomChange =
        birthBearerEmploymentFreedomLoss :=
  ⟨execution.selfActionExact, execution.controllerExact,
    execution.employmentInterestExact, execution.employmentPhaseNonzero,
    execution.freedomChangeExact⟩

theorem exactRoleRelease :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .source = .employed ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .target = .released ∧
      birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .source ≠
        birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .target :=
  ⟨execution.sourceRoleExact, execution.targetRoleExact,
    execution.selfActionPower.freedom_ne⟩

theorem actionControllerSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          execution.exerciseActionValue.1 :=
  birthBearerExitExerciseController.controller_provenance
    execution.controllerExact

theorem employmentRelationSourceTrace :
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
  execution.selfActionPower.interest_exact_state_provenance

theorem noncaptureAndIndependentControlRemain :
    (¬ birthBearerNoCapture.Captures execution.exerciseActionValue.1) ∧
      execution.realEmploymentLoss = birthBearerEmploymentLoss ∧
      birthBearerEmployer ≠ birthBearerWorker :=
  ⟨execution.responseActionUncaptured, execution.realEmploymentLossExact,
    execution.distinctEmploymentController⟩

theorem paymentAndSettlementRemain :
    execution.existingPaymentOccurrence =
        existingActualExit.paymentOccurrence ∧
      execution.existingActualSettlement =
        existingActualExit.actualSettlement :=
  ⟨execution.existingPaymentOccurrenceExact,
    execution.existingActualSettlementExact⟩

end SourceGeneratedContributionCapacityBearerLeaveExecutionAt

theorem bearerLeaveExecution_hasNoCallerPayload
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :
    True := by
  let execution :=
    sourceGeneratedContributionCapacityBearerLeaveExecutionAt depth
      existingActualExit
  fail_if_success exact execution.action
  fail_if_success exact execution.controller
  fail_if_success exact execution.affected
  fail_if_success exact execution.relation
  fail_if_success exact execution.target
  fail_if_success exact execution.disposition
  fail_if_success exact execution.registry
  fail_if_success exact execution.future
  trivial

end
end M14SourceGeneratedContributionCapacityBearerLeaveExecution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerLeaveExecution.sourceGeneratedContributionCapacityBearerLeaveExecutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerLeaveExecution.SourceGeneratedContributionCapacityBearerLeaveExecutionAt.exactSelfActionPower
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerLeaveExecution.birthBearerIndependentExitFalseExecutionPower_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerLeaveExecution.birthBearerNewJobFalseExecutionPower_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerLeaveExecution.birthBearerSelfActionPower_relation_eq_employment
