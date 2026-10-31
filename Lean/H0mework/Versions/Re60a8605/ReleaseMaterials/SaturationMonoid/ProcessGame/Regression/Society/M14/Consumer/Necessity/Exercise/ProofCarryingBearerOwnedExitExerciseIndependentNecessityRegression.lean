import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Exercise.Producer.SourceGeneratedBearerOwnedExitExerciseIndependentNecessity
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Service.ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression

/-!
# Direct consumer of bearer-owned exact exit exercise necessity

This certificate consumes the root-read-generated `.t1` leave action together
with its exact controller, source trace, payment/service/bearer alignment,
external responsibility and paid next.  It also retains the real `.t0`
employment-termination action and proves that neither that action nor any
opportunity/renewal/service fragment can retype it as bearer-owned exercise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingBearerOwnedExitExerciseIndependentNecessityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
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
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity
open M14ProofCarryingServiceBeneficiaryBearerAlignmentIndependentNecessityRegression
open M14SourceGeneratedBearerOwnedExitExerciseIndependentNecessity

abbrev CanonicalBearerOwnedExerciseCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
    sourceIndex index

def canonicalBearerOwnedExerciseCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index :=
  sourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
    sourceIndex index

abbrev CanonicalTerminationAlignmentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ExactEmploymentTerminationAsBearerLeaveExerciseAt oldVisit sourceIndex index

abbrev CanonicalBearerFeasibleEdgeAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ExactFeasibleExitEdgeAt
    (birthBearerGeometryCompilerAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))
    ExitFutureCode.leave
    (firstSlotAt
      (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index))

structure BearerOwnedExitExerciseAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (countermodel : CanonicalBearerOwnedExerciseCountermodelAt oldVisit
      sourceIndex index) : Prop where
  priorServiceAudit : ServiceBeneficiaryBearerAlignmentAuditAt
    countermodel.serviceCountermodel
  positiveRootRead :
    countermodel.positiveExercise.bearerExit =
        Classical.choice countermodel.positiveExercise.bearerRootRead.down ∧
      countermodel.positiveExercise.exitAction =
        countermodel.positiveExercise.bearerExit.exitExerciseAction ∧
      countermodel.positiveExercise.tenureAlignment.bearerExit =
        countermodel.positiveExercise.bearerExit
  exactActionAuthority :
    countermodel.positiveExercise.exitAction =
        birthBearerExactExitExerciseAction ∧
      birthBearerExitExerciseController.ControllerAt
        countermodel.positiveExercise.exitAction birthBearerWorker ∧
      countermodel.positiveExercise.exitAction.1 =
        countermodel.positiveExercise.bearerExit.actionableRenewal.code ∧
      countermodel.positiveExercise.exitAction.1 = ExitFutureCode.leave
  exactActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          countermodel.positiveExercise.exitAction.1
  exactRenewalAndFeasibleFromRootRead :
    countermodel.positiveExercise.actionableRenewal =
        countermodel.positiveExercise.bearerExit.actionableRenewal ∧
      countermodel.positiveExercise.feasibleEdge =
        countermodel.positiveExercise.bearerExit.feasibleEdge
  exactOpportunity :
    countermodel.positiveExercise.opportunity.code = ExitFutureCode.leave ∧
      ActionableAt birthBearerExitRelationCompiler.futureIdle
        (birthBearerExitRelationCompiler.futureCodesAt
          birthBearerIndependentExitRelation .target) .leave
  literalTenureService :
    countermodel.positiveExercise.tenureAlignment.channelSlot =
        firstSlotAt
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index) ∧
      HEq countermodel.positiveExercise.tenureAlignment.channelServiceReceipt
        countermodel.positiveExercise.bearerExit.feasibleEdge.serviceReceipt
  actionPaymentBearerIdentity :
    PurchasingPowerStandingAt.counterparty
          birthBearerExitCapacityProgram.purchasingPowerStanding =
        birthBearerWorker ∧
      exchangeLaw.bearerOfActor birthBearerWorker =
        countermodel.serviceCountermodel.originalBirthAdmission.obligation.bearer
  realTerminationAction :
    countermodel.realTerminationAction = birthBearerExactEmploymentAction ∧
      birthBearerEmploymentController.ControllerAt
        countermodel.realTerminationAction birthBearerEmployer ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = birthBearerEmploymentController.actionState
            Lifecycle.actualEventGame.source ∧
          birthBearerEmploymentController.actionAdmittedAt
            countermodel.realTerminationAction.1)
  terminationControllerIsNotBearer :
    birthBearerEmployer ≠ birthBearerWorker
  completeOpportunityAndServiceRemain :
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
        index)
  externalAuthorityAndNext :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          countermodel.serviceCountermodel.actualExit) ∧
      IsEmpty (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        countermodel.serviceCountermodel.outerRootEvent.occurrence.1) ∧
      countermodel.serviceCountermodel.postPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index + 1)
  outerAndEmbeddedOccurrencesRemainLayered :
    countermodel.serviceCountermodel.outerRootEvent =
        countermodel.serviceCountermodel.futureBirth.postRootEvent ∧
      countermodel.serviceCountermodel.embeddedM9RootEvent =
        countermodel.serviceCountermodel.embeddedM9Payment.rootOccurrence ∧
      countermodel.serviceCountermodel.embeddedM9Payment =
        countermodel.serviceCountermodel.actualExit.paymentOccurrence
  terminationAlignmentEmpty : IsEmpty
    (CanonicalTerminationAlignmentAt oldVisit sourceIndex index)
  opportunityCannotReconstruct : IsEmpty
    (PowerOpportunityAt birthBearerExitRelationCompiler birthBearerWorker
        birthBearerIndependentExitRelation .target →
      CanonicalTerminationAlignmentAt oldVisit sourceIndex index)
  actionableRenewalCannotReconstruct : IsEmpty
    ((birthBearerGeometryCompilerAt
        (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index)
        ).SourceGeneratedActionableExitRenewalAt →
      CanonicalTerminationAlignmentAt oldVisit sourceIndex index)
  realTerminationCannotReconstruct : IsEmpty
    (birthBearerEmploymentController.ExactActionSeed →
      CanonicalTerminationAlignmentAt oldVisit sourceIndex index)
  wholeCarrierCannotReconstruct : IsEmpty
    (CanonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index →
      CanonicalTerminationAlignmentAt oldVisit sourceIndex index)

theorem bearerOwnedExitExerciseAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    BearerOwnedExitExerciseAuditAt
      (canonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex
        index) := by
  let countermodel :=
    canonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index
  have priorAudit : ServiceBeneficiaryBearerAlignmentAuditAt
      countermodel.serviceCountermodel := by
    rw [countermodel.serviceCountermodelExact]
    exact serviceBeneficiaryBearerAlignmentAuditAt oldVisit sourceIndex index
  have opportunityAndService :=
    countermodel.realTerminationAndCompleteOpportunityRemain
  have external := countermodel.paymentServiceConsumerLiabilityAndNextRemain
  exact
    { priorServiceAudit := priorAudit
      positiveRootRead :=
        ⟨countermodel.positiveExercise.bearerExitFromRootRead,
          countermodel.positiveExercise.exitActionFromRootRead,
          countermodel.positiveExercise.tenureBearerExitFromSameRoot⟩
      exactActionAuthority :=
        ⟨countermodel.positiveExercise.exitActionCanonicalExact,
          countermodel.positiveExercise.controllerExact,
          countermodel.positiveExercise.actionCode_eq_renewalCode,
          countermodel.positiveExercise.actionCode_eq_leave⟩
      exactActionSourceTrace := countermodel.positiveExercise.sourceTrace
      exactRenewalAndFeasibleFromRootRead :=
        ⟨countermodel.positiveExercise.actionableRenewalFromRootRead,
          countermodel.positiveExercise.feasibleEdgeFromRootRead⟩
      exactOpportunity :=
        ⟨rfl, countermodel.positiveExercise.opportunity.actionable⟩
      literalTenureService := by
        refine ⟨countermodel.positiveExercise.tenureAlignment
          |>.channelSlot_eq_exitSlot, ?_⟩
        have receipt := countermodel.positiveExercise.tenureAlignment
          |>.channelServiceReceipt_eq_exitServiceReceipt
        rw [countermodel.positiveExercise.tenureBearerExitFromSameRoot] at receipt
        exact receipt
      actionPaymentBearerIdentity :=
        ⟨countermodel.positiveExercise.tenureAlignment
            |>.bearerStandingCounterparty_eq_exitWorker,
          countermodel.serviceCountermodel
            |>.exitWorkerBearer_eq_originalBirthBearer⟩
      realTerminationAction :=
        ⟨countermodel.realTerminationActionExact,
          countermodel.realTerminationControllerExact,
          countermodel.realTerminationTrace⟩
      terminationControllerIsNotBearer :=
        birthBearerEmployer_ne_birthBearerWorker
      completeOpportunityAndServiceRemain :=
        ⟨opportunityAndService.2.2.1,
          opportunityAndService.2.2.2.1,
          opportunityAndService.2.2.2.2.1,
          opportunityAndService.2.2.2.2.2.1⟩
      externalAuthorityAndNext :=
        ⟨external.2.2.1,
          external.2.2.2.1,
          external.2.2.2.2.1,
          external.2.2.2.2.2⟩
      outerAndEmbeddedOccurrencesRemainLayered :=
        countermodel.serviceCountermodel
          |>.outerAndEmbeddedOccurrencesRemainLayered
      terminationAlignmentEmpty := countermodel.terminationAlignmentDeleted
      opportunityCannotReconstruct :=
        opportunityCannotReconstructTerminationAsBearerExercise oldVisit
          sourceIndex index
      actionableRenewalCannotReconstruct :=
        actionableRenewalCannotReconstructTerminationAsBearerExercise oldVisit
          sourceIndex index
      realTerminationCannotReconstruct :=
        realTerminationActionCannotReconstructBearerExercise oldVisit
          sourceIndex index
      wholeCarrierCannotReconstruct :=
        completeRemainingCarrierCannotRetypeTerminationAsBearerExercise
          oldVisit sourceIndex index }

theorem exerciseFragmentsCannotReconstructTerminationAlignment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let countermodel :=
      canonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index
    IsEmpty
        (CanonicalBearerFeasibleEdgeAt oldVisit sourceIndex index →
          CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        (BearerOwnedExerciseTenureAlignmentAt oldVisit sourceIndex index →
          CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        ((PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex index
            countermodel.serviceCountermodel.outerRootEvent
            countermodel.serviceCountermodel.actualExit) →
          CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        ((countermodel.serviceCountermodel.postPayment.nextPaidBy =
            contributionCapacityPostSettlementRenewalEmitted oldVisit
              sourceIndex
              (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex index +
                1)) →
          CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        ((ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
            countermodel.serviceCountermodel.tenureChannel) →
          CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
      IsEmpty
        (ExactBearerOwnedExitExerciseAuthorityAt oldVisit sourceIndex index →
          CanonicalTerminationAlignmentAt oldVisit sourceIndex index) := by
  let countermodel :=
    canonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index
  let deleted := countermodel.terminationAlignmentDeleted
  exact
    ⟨⟨fun reconstruct => deleted.false
        (reconstruct countermodel.positiveExercise.feasibleEdge)⟩,
      ⟨fun reconstruct => deleted.false
        (reconstruct countermodel.positiveExercise.tenureAlignment)⟩,
      ⟨fun reconstruct => deleted.false
        (reconstruct countermodel.serviceCountermodel.externalLiability)⟩,
      ⟨fun reconstruct => deleted.false
        (reconstruct countermodel.serviceCountermodel.nextPaidByExact)⟩,
      ⟨fun reconstruct => deleted.false
        (reconstruct countermodel.serviceCountermodel.tenureConsumer)⟩,
      ⟨fun reconstruct => deleted.false
        (reconstruct countermodel.positiveExercise)⟩⟩

structure ProofCarryingBearerOwnedExitExerciseIndependentNecessityCertificate :
    Prop where
  everyCountermodel : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty (CanonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex
      index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    BearerOwnedExitExerciseAuditAt
      (canonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index)
  everyFragmentNoReconstruction :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      let countermodel :=
        canonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index
      IsEmpty
          (CanonicalBearerFeasibleEdgeAt oldVisit sourceIndex index →
            CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
        IsEmpty
          (BearerOwnedExerciseTenureAlignmentAt oldVisit sourceIndex index →
            CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
        IsEmpty
          ((PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
              index countermodel.serviceCountermodel.outerRootEvent
              countermodel.serviceCountermodel.actualExit) →
            CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
        IsEmpty
          ((countermodel.serviceCountermodel.postPayment.nextPaidBy =
              contributionCapacityPostSettlementRenewalEmitted oldVisit
                sourceIndex
                (serviceBeneficiaryAlignmentCurrentAt oldVisit sourceIndex
                    index + 1)) →
            CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
        IsEmpty
          ((ProofCarryingContributionCapacityPostSettlementChannelConsumerAt
              countermodel.serviceCountermodel.tenureChannel) →
            CanonicalTerminationAlignmentAt oldVisit sourceIndex index) ∧
        IsEmpty
          (ExactBearerOwnedExitExerciseAuthorityAt oldVisit sourceIndex index →
            CanonicalTerminationAlignmentAt oldVisit sourceIndex index)

theorem proofCarryingBearerOwnedExitExerciseIndependentNecessityDirectConsumer :
    ProofCarryingBearerOwnedExitExerciseIndependentNecessityCertificate where
  everyCountermodel := fun oldVisit sourceIndex index =>
    ⟨canonicalBearerOwnedExerciseCountermodelAt oldVisit sourceIndex index⟩
  everyAudit := bearerOwnedExitExerciseAuditAt
  everyFragmentNoReconstruction :=
    exerciseFragmentsCannotReconstructTerminationAlignment

end
end M14ProofCarryingBearerOwnedExitExerciseIndependentNecessityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBearerOwnedExitExerciseIndependentNecessityRegression.bearerOwnedExitExerciseAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBearerOwnedExitExerciseIndependentNecessityRegression.exerciseFragmentsCannotReconstructTerminationAlignment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBearerOwnedExitExerciseIndependentNecessityRegression.proofCarryingBearerOwnedExitExerciseIndependentNecessityDirectConsumer
