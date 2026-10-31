import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Execution.Producer.SourceGeneratedContributionCapacityBearerLeaveExecution

/-!
# Source-generated bearer role-independent continuation

The exact `.leave` action is read as a target-side continuation of the
generated phase-zero independent-exit relation.  That relation keeps role
`.independent`; its domain-native future witness survives independently of
price capture, while capture-adjusted actionability exists only under the
installed noncapture compiler.

Phase zero is essential here: this carrier is a future continuation, not a
second action power over the independent relation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation

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
open M14SourceGeneratedContributionCapacityBearerLeaveExecution

@[simp] theorem birthBearerIndependentExitRelation_phase_exact :
    birthBearerExitRelationCompiler.phaseStep
        birthBearerIndependentExitRelation = 0 :=
  rfl

@[simp] theorem birthBearerIndependentExitRelation_sourceRole_exact :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
        .source = .independent :=
  rfl

@[simp] theorem birthBearerIndependentExitRelation_targetRole_exact :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
        .target = .independent :=
  rfl

abbrev BirthBearerRoleIndependentActionableExit :=
  birthBearerExitCapacityProgram.exitCone.ActionableExitAt

abbrev BirthBearerFullCaptureActionableExit :=
  birthBearerCapturedProgram.exitCone.ActionableExitAt

/-- Full capture removes capture-adjusted actionability, not the underlying
generated target future continuation. -/
theorem birthBearerFullCaptureActionableExit_isEmpty :
    IsEmpty BirthBearerFullCaptureActionableExit :=
  birthBearerCapturedProgram.exitCone.isEmpty_actionableExit_iff_fullPriceCapture.mpr
    birthBearerCapturedProgram_fullPriceCapture

/-- Action-indexed continuation carrier at one existing actual-exit
authority.  No predecessor, next occurrence or completed future is supplied
by the caller. -/
structure SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
    (depth : Nat)
    (existingActualExit : PeriodicActualServiceExitAt depth)
    (exerciseAction :
      birthBearerExitExerciseController.ExactActionSeed) : Type 18 where
  private mk ::
  response :
    SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit exerciseAction
  actionableExit : BirthBearerRoleIndependentActionableExit
  actionableExitExact : actionableExit = birthBearerActionableExit
  actionableCodeExact : actionableExit.1 = exerciseAction.1
  futureContinuation :
    birthBearerExitRelationCompiler.FutureContinuationAt
      birthBearerIndependentExitRelation.1 .target exerciseAction.1
  futureContinuationWitness :
    birthBearerExitRelationCompiler.FutureContinuationWitnessAt
      birthBearerIndependentExitRelation.1 .target exerciseAction.1
        futureContinuation
  independentInterestExact :
    birthBearerExitRelationCompiler.GeneratedInterestAt birthBearerWorker
      birthBearerIndependentExitRelation
  independentPhaseExact :
    birthBearerExitRelationCompiler.phaseStep
      birthBearerIndependentExitRelation = 0
  sourceRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
      .source = .independent
  targetRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
      .target = .independent
  actionUncaptured : ¬ birthBearerNoCapture.Captures exerciseAction.1
  independentRelationCannotBeExecution :
    IsEmpty BirthBearerIndependentExitFalseExecutionPower
  existingPaymentOccurrence : PeriodicSourceBackedPaymentAt depth
  existingPaymentOccurrenceExact : existingPaymentOccurrence =
    existingActualExit.paymentOccurrence
  existingActualSettlement : ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) debited (serviceCompilerAt depth)
  existingActualSettlementExact : existingActualSettlement =
    existingActualExit.actualSettlement

abbrev CanonicalContributionCapacityBearerRoleIndependentContinuationAt
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :=
  SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
    depth existingActualExit
      (sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
        depth existingActualExit).exerciseActionValue

def sourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :
    CanonicalContributionCapacityBearerRoleIndependentContinuationAt depth
      existingActualExit := by
  let response :=
    sourceGeneratedContributionCapacityBearerExerciseNoncaptureResponseAt
      depth existingActualExit
  exact
    { response := response
      actionableExit := birthBearerActionableExit
      actionableExitExact := rfl
      actionableCodeExact := rfl
      futureContinuation := PUnit.unit
      futureContinuationWitness := trivial
      independentInterestExact := birthBearerIndependentExitInterest
      independentPhaseExact :=
        birthBearerIndependentExitRelation_phase_exact
      sourceRoleExact :=
        birthBearerIndependentExitRelation_sourceRole_exact
      targetRoleExact :=
        birthBearerIndependentExitRelation_targetRole_exact
      actionUncaptured := response.actionUncaptured
      independentRelationCannotBeExecution :=
        birthBearerIndependentExitFalseExecutionPower_isEmpty
      existingPaymentOccurrence := response.existingPaymentOccurrence
      existingPaymentOccurrenceExact :=
        response.existingPaymentOccurrenceExact
      existingActualSettlement := response.existingActualSettlement
      existingActualSettlementExact :=
        response.existingActualSettlementExact }

namespace SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt

variable {depth : Nat} {existingActualExit : PeriodicActualServiceExitAt depth}
  {exerciseAction : birthBearerExitExerciseController.ExactActionSeed}
  (continuation :
    SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
      depth existingActualExit exerciseAction)

include continuation

def exerciseActionValue
    (_continuation :
      SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
        depth existingActualExit exerciseAction) :
    birthBearerExitExerciseController.ExactActionSeed :=
  exerciseAction

theorem exactRoleIndependentContinuation :
    continuation.actionableExit.1 = continuation.exerciseActionValue.1 ∧
      birthBearerExitRelationCompiler.GeneratedInterestAt birthBearerWorker
        birthBearerIndependentExitRelation ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerIndependentExitRelation = 0 ∧
      birthBearerExitRelationCompiler.roleAt
          birthBearerIndependentExitRelation .source = .independent ∧
      birthBearerExitRelationCompiler.roleAt
          birthBearerIndependentExitRelation .target = .independent ∧
      Nonempty
        (birthBearerExitRelationCompiler.FutureContinuationAt
          birthBearerIndependentExitRelation.1 .target
            continuation.exerciseActionValue.1) ∧
      ¬ birthBearerNoCapture.Captures
        continuation.exerciseActionValue.1 :=
  ⟨continuation.actionableCodeExact,
    continuation.independentInterestExact,
    continuation.independentPhaseExact,
    continuation.sourceRoleExact,
    continuation.targetRoleExact,
    ⟨continuation.futureContinuation⟩,
    continuation.actionUncaptured⟩

theorem witnessedFutureContinuation :
    ∃ future : birthBearerExitRelationCompiler.FutureContinuationAt
        birthBearerIndependentExitRelation.1 .target
          continuation.exerciseActionValue.1,
      birthBearerExitRelationCompiler.FutureContinuationWitnessAt
        birthBearerIndependentExitRelation.1 .target
          continuation.exerciseActionValue.1 future :=
  ⟨continuation.futureContinuation,
    continuation.futureContinuationWitness⟩

omit continuation in
theorem targetFutureBoundary_mem_actualOccurrence :
    birthBearerExitRelationCompiler.futureBoundaryState
        birthBearerIndependentExitRelation.1 .target ∈
      Lifecycle.actualEventGame.occurrence.trace :=
  birthBearerExitRelationCompiler.futureBoundaryState_mem_occurrence
    birthBearerIndependentExitRelation .target

theorem independentRelationSourceTrace :
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
        birthBearerIndependentExitRelation :=
  continuation.independentInterestExact.exact_state_provenance

theorem paymentAndSettlementRemain :
    continuation.existingPaymentOccurrence =
        existingActualExit.paymentOccurrence ∧
      continuation.existingActualSettlement =
        existingActualExit.actualSettlement :=
  ⟨continuation.existingPaymentOccurrenceExact,
    continuation.existingActualSettlementExact⟩

end SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt

theorem bearerRoleIndependentContinuation_hasNoCallerPayload
    (depth : Nat) (existingActualExit : PeriodicActualServiceExitAt depth) :
    True := by
  let continuation :=
    sourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
      depth existingActualExit
  fail_if_success exact continuation.action
  fail_if_success exact continuation.relation
  fail_if_success exact continuation.capture
  fail_if_success exact continuation.payment
  fail_if_success exact continuation.next
  fail_if_success exact continuation.target
  fail_if_success exact continuation.registry
  fail_if_success exact continuation.future
  trivial

end
end M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation.sourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation.SourceGeneratedContributionCapacityBearerRoleIndependentContinuationAt.exactRoleIndependentContinuation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation.birthBearerFullCaptureActionableExit_isEmpty
