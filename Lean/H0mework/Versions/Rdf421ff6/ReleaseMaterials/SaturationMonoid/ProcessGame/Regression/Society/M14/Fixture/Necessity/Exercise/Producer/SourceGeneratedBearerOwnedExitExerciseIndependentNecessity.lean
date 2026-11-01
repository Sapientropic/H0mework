import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Service.Producer.SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity

/-!
# Independent necessity of bearer-owned exact exit exercise

The existing post-settlement `.birthBearerExit` face already carries a paid,
routed, serviced and uncaptured `.leave` opportunity.  This module consumes
the exact action seed now generated inside that same root-read carrier and
separates it from the existing `.t0` employment-termination action.

The countermodel therefore retains a real actual action and every operational
exit axis while rejecting its retyping as the `.t1` bearer's leave exercise.
No action, controller, code, bearer, Payment, target or future is accepted at
the producer mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedBearerOwnedExitExerciseIndependentNecessity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity

abbrev BearerOwnedExerciseBearerExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ServiceBeneficiaryAlignmentBearerExitAt oldVisit sourceIndex index

abbrev BearerOwnedExerciseTenureAlignmentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  TenureServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index

/-! ## Root-read-generated positive authority -/

/--
One exact exercise authority.  Its occurrence identity is the outer
post-root face/rootRead; the recurring local action seed is only source
material, exactly as the recurring local payment receipt is wrapped by each
temporal Payment occurrence.
-/
structure ExactBearerOwnedExitExerciseAuthorityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 24 where
  private mk ::
  bearerFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  bearerFaceExact : bearerFace =
    serviceBeneficiaryAlignmentBearerFaceAt oldVisit sourceIndex index
  bearerRootRead : PLift (Nonempty
    (BearerOwnedExerciseBearerExitAt oldVisit sourceIndex index))
  bearerRootReadExact : bearerRootRead =
    serviceBeneficiaryAlignmentBearerRootReadAt oldVisit sourceIndex index
  bearerExit : BearerOwnedExerciseBearerExitAt oldVisit sourceIndex index
  bearerExitFromRootRead : bearerExit = Classical.choice bearerRootRead.down
  exitAction : birthBearerExitExerciseController.ExactActionSeed
  exitActionFromRootRead : exitAction = bearerExit.exitExerciseAction
  exitActionCanonicalExact : exitAction =
    birthBearerExactExitExerciseAction
  controllerExact : birthBearerExitExerciseController.ControllerAt
    exitAction birthBearerWorker
  actionCode_eq_renewalCode :
    exitAction.1 = bearerExit.actionableRenewal.code
  actionCode_eq_leave : exitAction.1 = ExitFutureCode.leave
  sourceTrace : ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
    state = birthBearerExitExerciseController.actionState
        Lifecycle.actualEventGame.source ∧
      birthBearerExitExerciseController.actionAdmittedAt exitAction.1
  actionableRenewal :
    (birthBearerGeometryCompilerAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
      ).SourceGeneratedActionableExitRenewalAt
  actionableRenewalFromRootRead : actionableRenewal =
    bearerExit.actionableRenewal
  feasibleEdge : ExactFeasibleExitEdgeAt
    (birthBearerGeometryCompilerAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
    ExitFutureCode.leave
    (firstSlotAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
  feasibleEdgeFromRootRead : feasibleEdge = bearerExit.feasibleEdge
  opportunity : PowerOpportunityAt birthBearerExitRelationCompiler
    birthBearerWorker birthBearerIndependentExitRelation .target
  tenureAlignment :
    BearerOwnedExerciseTenureAlignmentAt oldVisit sourceIndex index
  tenureBearerExitFromSameRoot : tenureAlignment.bearerExit = bearerExit

/-- Sole positive producer; all values are selected from the fixed root face. -/
def exactBearerOwnedExitExerciseAuthorityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ExactBearerOwnedExitExerciseAuthorityAt oldVisit sourceIndex index := by
  let bearerRootRead :=
    serviceBeneficiaryAlignmentBearerRootReadAt oldVisit sourceIndex index
  let bearerExit := Classical.choice bearerRootRead.down
  let tenureAlignment :=
    tenureServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex index
  exact
    { bearerFace :=
        serviceBeneficiaryAlignmentBearerFaceAt oldVisit sourceIndex index
      bearerFaceExact := rfl
      bearerRootRead := bearerRootRead
      bearerRootReadExact := rfl
      bearerExit := bearerExit
      bearerExitFromRootRead := rfl
      exitAction := bearerExit.exitExerciseAction
      exitActionFromRootRead := rfl
      exitActionCanonicalExact := bearerExit.exitExerciseActionExact
      controllerExact := bearerExit.exitExerciseControllerExact
      actionCode_eq_renewalCode :=
        bearerExit.exitExerciseCode_eq_renewalCode
      actionCode_eq_leave := by
        rw [bearerExit.exitExerciseActionExact]
        rfl
      sourceTrace := bearerExit.exitExerciseSourceProvenance
      actionableRenewal := bearerExit.actionableRenewal
      actionableRenewalFromRootRead := rfl
      feasibleEdge := bearerExit.feasibleEdge
      feasibleEdgeFromRootRead := rfl
      opportunity := birthBearerLeavePowerOpportunity
      tenureAlignment := tenureAlignment
      tenureBearerExitFromSameRoot := rfl }

/-! ## Real action which cannot be retyped as bearer leave exercise -/

/--
The forbidden alignment retains the exact bearer rootRead and the real
employment-termination action.  Only its final controller-to-bearer incidence
is impossible; the countermodel never claims that termination is a leave
action.
-/
structure ExactEmploymentTerminationAsBearerLeaveExerciseAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 24 where
  private mk ::
  bearerRootRead : PLift (Nonempty
    (BearerOwnedExerciseBearerExitAt oldVisit sourceIndex index))
  bearerRootReadExact : bearerRootRead =
    serviceBeneficiaryAlignmentBearerRootReadAt oldVisit sourceIndex index
  bearerExit : BearerOwnedExerciseBearerExitAt oldVisit sourceIndex index
  bearerExitFromRootRead : bearerExit = Classical.choice bearerRootRead.down
  opportunity : PowerOpportunityAt birthBearerExitRelationCompiler
    birthBearerWorker birthBearerIndependentExitRelation .target
  terminationAction : birthBearerEmploymentController.ExactActionSeed
  terminationActionExact : terminationAction =
    birthBearerExactEmploymentAction
  terminationControllerExact :
    birthBearerEmploymentController.ControllerAt terminationAction
      birthBearerEmployer
  terminationController_eq_exitBearer :
    birthBearerEmployer = birthBearerWorker

theorem employmentTerminationAsBearerLeaveExercise_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty (ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit
      sourceIndex index) :=
  ⟨fun falseAlignment =>
    birthBearerEmployer_ne_birthBearerWorker
      falseAlignment.terminationController_eq_exitBearer⟩

/-! ## Full same-occurrence countermodel -/

structure SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 25 where
  private mk ::
  serviceCountermodel :
    SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex index
  serviceCountermodelExact : serviceCountermodel =
    sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex index
  positiveExercise : ExactBearerOwnedExitExerciseAuthorityAt oldVisit
    sourceIndex index
  positiveExerciseExact : positiveExercise =
    exactBearerOwnedExitExerciseAuthorityAt oldVisit sourceIndex index
  realTerminationAction : birthBearerEmploymentController.ExactActionSeed
  realTerminationActionExact : realTerminationAction =
    birthBearerExactEmploymentAction
  realTerminationControllerExact :
    birthBearerEmploymentController.ControllerAt realTerminationAction
      birthBearerEmployer
  realTerminationTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerEmploymentController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerEmploymentController.actionAdmittedAt
          realTerminationAction.1
  terminationAlignmentDeleted : IsEmpty
    (ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit sourceIndex
      index)

/-- Sole producer from one already generated post-root occurrence. -/
def sourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
      sourceIndex index :=
  let serviceCountermodel :=
    sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex index
  let positiveExercise :=
    exactBearerOwnedExitExerciseAuthorityAt oldVisit sourceIndex index
  { serviceCountermodel := serviceCountermodel
    serviceCountermodelExact := rfl
    positiveExercise := positiveExercise
    positiveExerciseExact := rfl
    realTerminationAction := birthBearerExactEmploymentAction
    realTerminationActionExact := rfl
    realTerminationControllerExact := rfl
    realTerminationTrace :=
      birthBearerEmploymentController.controller_provenance rfl
    terminationAlignmentDeleted :=
      employmentTerminationAsBearerLeaveExercise_isEmpty oldVisit sourceIndex
        index }

namespace SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (countermodel :
    SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
      sourceIndex index)

include countermodel

/-- The positive authority is literally carried by the installed bearer
rootRead, including its action, controller, code and source trace. -/
theorem positiveExerciseGeneratedFromRootRead :
    countermodel.positiveExercise.bearerFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      countermodel.positiveExercise.exitAction =
        countermodel.positiveExercise.bearerExit.exitExerciseAction ∧
      birthBearerExitExerciseController.ControllerAt
        countermodel.positiveExercise.exitAction birthBearerWorker ∧
      countermodel.positiveExercise.exitAction.1 =
        countermodel.positiveExercise.bearerExit.actionableRenewal.code ∧
      countermodel.positiveExercise.exitAction.1 = ExitFutureCode.leave ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = birthBearerExitExerciseController.actionState
            Lifecycle.actualEventGame.source ∧
          birthBearerExitExerciseController.actionAdmittedAt
            countermodel.positiveExercise.exitAction.1) := by
  rw [countermodel.positiveExercise.bearerFaceExact]
  exact ⟨rfl,
    countermodel.positiveExercise.exitActionFromRootRead,
    countermodel.positiveExercise.controllerExact,
    countermodel.positiveExercise.actionCode_eq_renewalCode,
    countermodel.positiveExercise.actionCode_eq_leave,
    countermodel.positiveExercise.sourceTrace⟩

/-- A genuine termination action and a complete leave opportunity both remain;
neither one alone supplies bearer-owned exercise authority. -/
theorem realTerminationAndCompleteOpportunityRemain :
    birthBearerEmploymentController.ControllerAt
        countermodel.realTerminationAction birthBearerEmployer ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = birthBearerEmploymentController.actionState
            Lifecycle.actualEventGame.source ∧
          birthBearerEmploymentController.actionAdmittedAt
            countermodel.realTerminationAction.1) ∧
      Nonempty (PowerOpportunityAt birthBearerExitRelationCompiler
        birthBearerWorker birthBearerIndependentExitRelation .target) ∧
      Nonempty
        ((birthBearerGeometryCompilerAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          ).SourceGeneratedActionableExitRenewalAt) ∧
      (birthBearerGeometryCompilerAt
        (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
        ).actionableExitCapacity = 1 ∧
      Nonempty (BearerOwnedExerciseTenureAlignmentAt oldVisit sourceIndex
        index) ∧
      IsEmpty (ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit
        sourceIndex index) :=
  ⟨countermodel.realTerminationControllerExact,
    countermodel.realTerminationTrace,
    ⟨countermodel.positiveExercise.opportunity⟩,
    ⟨countermodel.positiveExercise.actionableRenewal⟩,
    countermodel.positiveExercise.bearerExit.exactCapacity,
    ⟨countermodel.positiveExercise.tenureAlignment⟩,
    countermodel.terminationAlignmentDeleted⟩

/-- Payment, service, external responsibility, the empty local ledger and the
unique paid next are inherited from the already certified same occurrence. -/
theorem paymentServiceConsumerLiabilityAndNextRemain :
    Nonempty (ExactFeasibleExitEdgeAt
        (geometryCompilerAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
        ExitFutureCode.leave
        (channelSlotAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          healthAuthority)) ∧
      Nonempty (RenewalResponsibilityConsumerAt
        (countermodel.serviceCountermodel.actualExit.paymentOccurrence.installed
          ).operationalAuthority) ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          countermodel.serviceCountermodel.actualExit) ∧
      IsEmpty (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        countermodel.serviceCountermodel.outerRootEvent.occurrence.1) ∧
      countermodel.serviceCountermodel.postPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index + 1) := by
  have health := countermodel.serviceCountermodel
    |>.healthPaymentRouteServiceConsumerRemain
  have outer := countermodel.serviceCountermodel
    |>.outerPaymentLiabilityAndNextRemain
  exact ⟨health.1, health.2.1,
    outer.2.2.1, outer.2.2.2.1, outer.2.2.2.2.1,
    outer.2.2.2.2.2⟩

theorem terminationAlignmentIsExactlyDeleted :
    IsEmpty (ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit
      sourceIndex index) :=
  countermodel.terminationAlignmentDeleted

end SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt

/-! ## No reconstruction and anti-smuggling controls -/

theorem opportunityCannotReconstructTerminationAsBearerExercise
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (PowerOpportunityAt birthBearerExitRelationCompiler birthBearerWorker
          birthBearerIndependentExitRelation .target →
        ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit
          sourceIndex index) :=
  ⟨fun reconstruct =>
    (employmentTerminationAsBearerLeaveExercise_isEmpty oldVisit sourceIndex
      index).false (reconstruct birthBearerLeavePowerOpportunity)⟩

theorem actionableRenewalCannotReconstructTerminationAsBearerExercise
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      ((birthBearerGeometryCompilerAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
          ).SourceGeneratedActionableExitRenewalAt →
        ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit
          sourceIndex index) :=
  ⟨fun reconstruct =>
    (employmentTerminationAsBearerLeaveExercise_isEmpty oldVisit sourceIndex
      index).false
        (reconstruct (birthBearerActionableExitRenewalAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)))⟩

theorem realTerminationActionCannotReconstructBearerExercise
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (birthBearerEmploymentController.ExactActionSeed →
        ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit
          sourceIndex index) :=
  ⟨fun reconstruct =>
    (employmentTerminationAsBearerLeaveExercise_isEmpty oldVisit sourceIndex
      index).false (reconstruct birthBearerExactEmploymentAction)⟩

theorem completeRemainingCarrierCannotRetypeTerminationAsBearerExercise
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
          sourceIndex index →
        ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit
          sourceIndex index) :=
  ⟨fun reconstruct =>
    (employmentTerminationAsBearerLeaveExercise_isEmpty oldVisit sourceIndex
      index).false
        (reconstruct
          (sourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt
            oldVisit sourceIndex index))⟩

theorem bearerOwnedExitExerciseProducer_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let generated :=
    sourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
      sourceIndex index
  fail_if_success exact generated.action
  fail_if_success exact generated.controller
  fail_if_success exact generated.code
  fail_if_success exact generated.bearer
  fail_if_success exact generated.payment
  fail_if_success exact generated.target
  fail_if_success exact generated.registry
  fail_if_success exact generated.future
  trivial

end
end M14SourceGeneratedBearerOwnedExitExerciseIndependentNecessity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBearerOwnedExitExerciseIndependentNecessity.exactBearerOwnedExitExerciseAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBearerOwnedExitExerciseIndependentNecessity.sourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBearerOwnedExitExerciseIndependentNecessity.completeRemainingCarrierCannotRetypeTerminationAsBearerExercise
