import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Producer.SourceGeneratedContributionCapacityBirthBearerExit

/-!
# Source-generated bearer-exercise noncapture response

One already generated periodic actual-exit authority regenerates the existing
bearer exit and its exact `.t1/.leave` action.  The response records that this
exact action is not captured by the bearer program, while the independent real
employment-loss action power remains present.  The existing full-price capture
program is retained as the same-action, zero-capacity countermodel.

This is a dependent response carrier, not an execution verdict, retaliation
registry, second occurrence, or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityBirthBearerExit

abbrev BirthBearerEmploymentLossAuthority :=
  SourceGeneratedEmploymentLossAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (controllerFace := Lifecycle.Universal.FixedAdapter.targetFace)
    (exitRelationCompiler := birthBearerExitRelationCompiler)
    (employmentController := birthBearerEmploymentController)
    birthBearerEmployer birthBearerWorker birthBearerEmploymentRelation

/-- Action-indexed response at one existing actual-exit authority. -/
structure SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
    (depth : Nat)
    (existingActualExit : PeriodicActualServiceExitAt depth)
    (exerciseAction :
      birthBearerExitExerciseController.ExactActionSeed) : Type 18 where
  private mk ::
  bearerExit : SourceGeneratedContributionCapacityBirthBearerExitAt depth
    existingActualExit
  bearerExitExact : bearerExit =
    sourceGeneratedContributionCapacityBirthBearerExitAt depth
      existingActualExit
  exerciseActionFromBearer : exerciseAction = bearerExit.exitExerciseAction
  exerciseActionExact : exerciseAction = birthBearerExactExitExerciseAction
  exerciseControllerExact :
    birthBearerExitExerciseController.ControllerAt exerciseAction
      birthBearerWorker
  actionUncaptured : ¬ birthBearerNoCapture.Captures exerciseAction.1
  employmentLoss : BirthBearerEmploymentLossAuthority
  employmentLossExact : employmentLoss = birthBearerEmploymentLoss
  employmentActionExact : employmentLoss.power.action =
    birthBearerExactEmploymentAction
  employmentControllerExact :
    birthBearerEmploymentController.ControllerAt employmentLoss.power.action
      birthBearerEmployer
  controllersDistinct : birthBearerEmployer ≠ birthBearerWorker
  actionFullCaptured : birthBearerFullCapture.Captures exerciseAction.1
  exactCapacity :
    (birthBearerGeometryCompilerAt depth).actionableExitCapacity = 1
  fullCapturedCapacity :
    (birthBearerCapturedGeometryCompilerAt depth).actionableExitCapacity = 0
  existingPaymentOccurrence : PeriodicSourceBackedPaymentAt depth
  existingPaymentOccurrenceExact : existingPaymentOccurrence =
    existingActualExit.paymentOccurrence
  existingActualSettlement : ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) debited (serviceCompilerAt depth)
  existingActualSettlementExact : existingActualSettlement =
    existingActualExit.actualSettlement

abbrev CanonicalContributionCapacityBearerExerciseNoncaptureResponseAt
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :=
  SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt depth
    existingActualExit
    (sourceGeneratedContributionCapacityBirthBearerExitAt depth
      existingActualExit).exitExerciseAction

/-- Sole producer from the already generated actual-exit authority. -/
def sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :
    CanonicalContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit := by
  let bearerExit :=
    sourceGeneratedContributionCapacityBirthBearerExitAt depth
      existingActualExit
  exact
    { bearerExit := bearerExit
      bearerExitExact := rfl
      exerciseActionFromBearer := rfl
      exerciseActionExact := bearerExit.exitExerciseActionExact
      exerciseControllerExact := bearerExit.exitExerciseControllerExact
      actionUncaptured := by
        simp [birthBearerNoCapture]
      employmentLoss := birthBearerEmploymentLoss
      employmentLossExact := rfl
      employmentActionExact := rfl
      employmentControllerExact := rfl
      controllersDistinct := birthBearerEmployer_ne_birthBearerWorker
      actionFullCaptured := by
        rw [bearerExit.exitExerciseActionExact]
        rfl
      exactCapacity := bearerExit.exactCapacity
      fullCapturedCapacity := bearerExit.capturedCapacity
      existingPaymentOccurrence := bearerExit.existingPaymentOccurrence
      existingPaymentOccurrenceExact :=
        bearerExit.existingPaymentOccurrence_eq
      existingActualSettlement := bearerExit.existingActualSettlement
      existingActualSettlementExact :=
        bearerExit.existingActualSettlement_eq }

namespace SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt

variable {depth : Nat} {existingActualExit : PeriodicActualServiceExitAt depth}
  {exerciseAction : birthBearerExitExerciseController.ExactActionSeed}
  (response :
    SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit exerciseAction)

include response

def exerciseActionValue
    (_response :
      SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
        depth existingActualExit exerciseAction) :
    birthBearerExitExerciseController.ExactActionSeed :=
  exerciseAction

theorem exactActionResponse :
    response.exerciseActionValue = response.bearerExit.exitExerciseAction ∧
      response.exerciseActionValue = birthBearerExactExitExerciseAction ∧
      birthBearerExitExerciseController.ControllerAt response.exerciseActionValue
        birthBearerWorker ∧
      ¬ birthBearerNoCapture.Captures response.exerciseActionValue.1 :=
  ⟨response.exerciseActionFromBearer, response.exerciseActionExact,
    response.exerciseControllerExact, response.actionUncaptured⟩

theorem exerciseActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          response.exerciseActionValue.1 :=
  birthBearerExitExerciseController.controller_provenance
    response.exerciseControllerExact

theorem realEmploymentLossRemains :
    response.employmentLoss = birthBearerEmploymentLoss ∧
      response.employmentLoss.power.action =
        birthBearerExactEmploymentAction ∧
      birthBearerEmploymentController.ControllerAt
        response.employmentLoss.power.action birthBearerEmployer ∧
      birthBearerEmployer ≠ birthBearerWorker :=
  ⟨response.employmentLossExact, response.employmentActionExact,
    response.employmentControllerExact, response.controllersDistinct⟩

theorem employmentActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerEmploymentController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerEmploymentController.actionAdmittedAt
          response.employmentLoss.power.action.1 :=
  response.employmentLoss.power.controller_exact_state_provenance

theorem fullCaptureCountermodel :
    birthBearerFullCapture.Captures response.exerciseActionValue.1 ∧
      (birthBearerGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt depth).actionableExitCapacity =
        0 :=
  ⟨response.actionFullCaptured, response.exactCapacity,
    response.fullCapturedCapacity⟩

theorem paymentAndSettlementRemain :
    response.existingPaymentOccurrence =
        existingActualExit.paymentOccurrence ∧
      response.existingActualSettlement =
        existingActualExit.actualSettlement :=
  ⟨response.existingPaymentOccurrenceExact,
    response.existingActualSettlementExact⟩

end SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt

theorem bearerExerciseNoncaptureResponse_hasNoCallerPayload
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :
    True := by
  let response :=
    sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit
  fail_if_success exact response.action
  fail_if_success exact response.controller
  fail_if_success exact response.captureVerdict
  fail_if_success exact response.target
  fail_if_success exact response.occurrence
  fail_if_success exact response.registry
  fail_if_success exact response.future
  trivial

end
end M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse.sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse.SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt.exactActionResponse
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse.SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt.fullCaptureCountermodel
