import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Consequence.Producer.SourceGeneratedBearerActionPaidConsequenceIndependentNecessity
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Exercise.ProofCarryingBearerOwnedExitExerciseIndependentNecessityRegression

/-!
# Direct consumer of bearer-action / paid-consequence necessity

The certificate consumes the action-bearing outer Payment itself: its native
write, root-read action, selected actual exit, embedded Payment/settlement,
external consumer/liability, successor and paid next.  It also consumes the
real termination action and the exact empty fibre preventing that action from
being reported as the paid bearer leave.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingBearerActionPaidConsequenceIndependentNecessityRegression

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
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity
open M14SourceGeneratedBearerOwnedExitExerciseIndependentNecessity
open M14ProofCarryingBearerOwnedExitExerciseIndependentNecessityRegression
open M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity

abbrev CanonicalBearerActionPaidConsequenceCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt oldVisit
    sourceIndex index

def canonicalBearerActionPaidConsequenceCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
      index :=
  sourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt oldVisit
    sourceIndex index

abbrev CanonicalTerminationPaymentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit sourceIndex index

structure BearerActionPaidConsequenceAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (countermodel : CanonicalBearerActionPaidConsequenceCountermodelAt oldVisit
      sourceIndex index) : Prop where
  priorExerciseAudit : BearerOwnedExitExerciseAuditAt
    countermodel.priorExercise
  outerEventAndWrite :
    countermodel.paidConsequence.outerRootEvent =
        contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
          index ∧
      countermodel.paidConsequence.nativeWrite =
        countermodel.paidConsequence.payment.write ∧
      countermodel.paidConsequence.nativeWrite =
        PLift.up
          countermodel.paidConsequence.outerRootEvent.occurrence.2.periodicExitGenerated
  paymentOwnsRootReadAction :
    countermodel.paidConsequence.payment.exerciseFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      countermodel.paidConsequence.payment.exerciseCarrier =
        Classical.choice
          countermodel.paidConsequence.payment.exerciseRootRead.down ∧
      countermodel.paidConsequence.payment.exerciseAction =
        countermodel.paidConsequence.payment.exerciseCarrier.exitExerciseAction ∧
      birthBearerExitExerciseController.ControllerAt
        countermodel.paidConsequence.payment.exerciseAction birthBearerWorker ∧
      countermodel.paidConsequence.payment.exerciseAction.1 =
        countermodel.paidConsequence.payment.exerciseCarrier.actionableRenewal.code
  exactPaidAction :
    countermodel.paidConsequence.exerciseAction =
        countermodel.paidConsequence.exerciseCarrier.exitExerciseAction ∧
      countermodel.paidConsequence.exerciseAction =
        countermodel.paidConsequence.payment.exerciseAction ∧
      birthBearerExitExerciseController.ControllerAt
        countermodel.paidConsequence.exerciseAction birthBearerWorker ∧
      countermodel.paidConsequence.exerciseAction.1 = ExitFutureCode.leave
  exactActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          countermodel.paidConsequence.exerciseAction.1
  writeSelectsActualExit :
    countermodel.paidConsequence.actualExit =
      Classical.choice countermodel.paidConsequence.nativeWrite.down
  embeddedPaymentAndSettlement :
    countermodel.paidConsequence.exerciseCarrier.existingPaymentOccurrence =
        countermodel.paidConsequence.actualExit.paymentOccurrence ∧
      countermodel.paidConsequence.exerciseCarrier.existingActualSettlement =
        countermodel.paidConsequence.actualExit.actualSettlement
  externalResponsibility :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        countermodel.paidConsequence.actualExit) ∧
      HEq countermodel.paidConsequence.externalLiability
        countermodel.paidConsequence.payment.liability
  successorAndPaidNext :
    HEq countermodel.paidConsequence.successor
        countermodel.paidConsequence.payment.successor ∧
      countermodel.paidConsequence.payment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
            sourceIndex index + 1)
  localLedgerEmpty : IsEmpty
    (OpenResponsibilityAt (JointSettlementNAt oldVisit)
      countermodel.paidConsequence.outerRootEvent.occurrence.1)
  outerEmbeddedDistinct :
    (Sum.inl countermodel.paidConsequence.outerRootEvent :
      ExactTemporalCausalRootEventAt
          (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
            ).toAuthoritativeRoot.toLedgerRoot
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
            index) ⊕
        ExactTemporalCausalRootEventAt
          jointRoot.toAuthoritativeRoot.toLedgerRoot
          (temporalVisitAt
            (contributionCapacityPostSettlementReachableCurrentAt oldVisit
              sourceIndex index))) ≠
      Sum.inr
        countermodel.paidConsequence.actualExit.paymentOccurrence.rootOccurrence
  realTerminationAndOpportunityRemain :
    birthBearerEmploymentController.ControllerAt
        countermodel.realTerminationAction birthBearerEmployer ∧
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
  terminationPaymentEmpty : IsEmpty
    (CanonicalTerminationPaymentAt oldVisit sourceIndex index)
  bareActionCannotReconstruct : IsEmpty
    (birthBearerExitExerciseController.ExactActionSeed →
      CanonicalTerminationPaymentAt oldVisit sourceIndex index)
  paymentReceiptCannotReconstruct : IsEmpty
    (SourceBackedUBIPaymentReceiptAt
        birthBearerExitCapacityProgram.purchasingPowerStanding
        ExitFutureCode.leave →
      CanonicalTerminationPaymentAt oldVisit sourceIndex index)
  actualExitCannotReconstruct : IsEmpty
    (PeriodicActualServiceExitAt
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex index) →
      CanonicalTerminationPaymentAt oldVisit sourceIndex index)
  liabilityCannotReconstruct : IsEmpty
    (PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex index
        countermodel.paidConsequence.outerRootEvent
        countermodel.paidConsequence.actualExit →
      CanonicalTerminationPaymentAt oldVisit sourceIndex index)
  fullCarrierCannotReconstruct : IsEmpty
    (CanonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
        index →
      CanonicalTerminationPaymentAt oldVisit sourceIndex index)

theorem bearerActionPaidConsequenceAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    BearerActionPaidConsequenceAuditAt
      (canonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
        index) := by
  let countermodel :=
    canonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
      index
  have priorAudit : BearerOwnedExitExerciseAuditAt
      countermodel.priorExercise := by
    rw [countermodel.priorExerciseExact]
    exact bearerOwnedExitExerciseAuditAt oldVisit sourceIndex index
  have paymentIncidence := countermodel.paidConsequence.payment
    |>.bearerExercisePaidConsequence_exact
  have remaining := countermodel.realTerminationAndAllNonTargetAxesRemain
  exact
    { priorExerciseAudit := priorAudit
      outerEventAndWrite :=
        ⟨countermodel.paidConsequence.outerRootEventExact,
          countermodel.paidConsequence.nativeWriteFromPayment,
          countermodel.paidConsequence.nativeWriteFromOuterEvent⟩
      paymentOwnsRootReadAction := paymentIncidence.1
        |> fun first =>
          ⟨first, paymentIncidence.2.1, paymentIncidence.2.2.1,
            paymentIncidence.2.2.2.1,
            paymentIncidence.2.2.2.2.1⟩
      exactPaidAction :=
        ⟨countermodel.paidConsequence.exerciseActionFromCarrier,
          countermodel.paidConsequence.exerciseActionFromPayment,
          countermodel.paidConsequence.exerciseControllerExact,
          countermodel.paidConsequence.exerciseCode_eq_leave⟩
      exactActionSourceTrace :=
        countermodel.paidConsequence.exerciseSourceTrace
      writeSelectsActualExit := countermodel.paidConsequence.actualExitExact
      embeddedPaymentAndSettlement :=
        ⟨countermodel.paidConsequence.exercisePaymentOccurrenceExact,
          countermodel.paidConsequence.exerciseSettlementExact⟩
      externalResponsibility :=
        ⟨countermodel.paidConsequence.externalSourceOwnership,
          countermodel.paidConsequence.externalRootConsumer,
          countermodel.paidConsequence.externalLiabilityFromPayment⟩
      successorAndPaidNext :=
        ⟨countermodel.paidConsequence.successorFromPayment,
          countermodel.paidConsequence.nextPaidByExact⟩
      localLedgerEmpty := countermodel.paidConsequence.localLedgerEmpty
      outerEmbeddedDistinct := countermodel.paidConsequence.outerEmbeddedDistinct
      realTerminationAndOpportunityRemain :=
        ⟨remaining.1, remaining.2.1, remaining.2.2.1,
          remaining.2.2.2.1, remaining.2.2.2.2.1⟩
      terminationPaymentEmpty := countermodel.terminationPaymentDeleted
      bareActionCannotReconstruct :=
        bareActionCannotReconstructTerminationPayment oldVisit sourceIndex
          index
      paymentReceiptCannotReconstruct :=
        paymentReceiptCannotReconstructTerminationPayment oldVisit sourceIndex
          index
      actualExitCannotReconstruct :=
        actualExitCannotReconstructTerminationPayment oldVisit sourceIndex
          index
      liabilityCannotReconstruct :=
        liabilityCannotReconstructTerminationPayment oldVisit sourceIndex
          index
      fullCarrierCannotReconstruct :=
        fullCarrierCannotReconstructTerminationPayment oldVisit sourceIndex
          index }

theorem nextPaymentOrPositiveIncidenceCannotReconstructTerminationPayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let countermodel :=
      canonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
        index
    IsEmpty
        ((countermodel.paidConsequence.payment.nextPaidBy =
            contributionCapacityPostSettlementRenewalEmitted oldVisit
              sourceIndex
              (contributionCapacityPostSettlementReachableCurrentAt oldVisit
                sourceIndex index + 1)) →
          CanonicalTerminationPaymentAt oldVisit sourceIndex index) ∧
      IsEmpty
        (CanonicalBearerActionPostPaymentAt oldVisit sourceIndex index →
          CanonicalTerminationPaymentAt oldVisit sourceIndex index) ∧
      IsEmpty
        (ExactBearerActionPaidConsequenceAt oldVisit sourceIndex index →
          CanonicalTerminationPaymentAt oldVisit sourceIndex index) := by
  let countermodel :=
    canonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
      index
  let deleted := countermodel.terminationPaymentDeleted
  exact
    ⟨⟨fun reconstruct => deleted.false
        (reconstruct countermodel.paidConsequence.nextPaidByExact)⟩,
      ⟨fun reconstruct => deleted.false
        (reconstruct countermodel.paidConsequence.payment)⟩,
      ⟨fun reconstruct => deleted.false
        (reconstruct countermodel.paidConsequence)⟩⟩

structure ProofCarryingBearerActionPaidConsequenceIndependentNecessityCertificate :
    Prop where
  everyCountermodel : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty (CanonicalBearerActionPaidConsequenceCountermodelAt oldVisit
      sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    BearerActionPaidConsequenceAuditAt
      (canonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
        index)
  everyFinalNoReconstruction :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      let countermodel :=
        canonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
          index
      IsEmpty
          ((countermodel.paidConsequence.payment.nextPaidBy =
              contributionCapacityPostSettlementRenewalEmitted oldVisit
                sourceIndex
                (contributionCapacityPostSettlementReachableCurrentAt oldVisit
                  sourceIndex index + 1)) →
            CanonicalTerminationPaymentAt oldVisit sourceIndex index) ∧
        IsEmpty
          (CanonicalBearerActionPostPaymentAt oldVisit sourceIndex index →
            CanonicalTerminationPaymentAt oldVisit sourceIndex index) ∧
        IsEmpty
          (ExactBearerActionPaidConsequenceAt oldVisit sourceIndex index →
            CanonicalTerminationPaymentAt oldVisit sourceIndex index)

theorem proofCarryingBearerActionPaidConsequenceIndependentNecessityDirectConsumer :
    ProofCarryingBearerActionPaidConsequenceIndependentNecessityCertificate where
  everyCountermodel := fun oldVisit sourceIndex index =>
    ⟨canonicalBearerActionPaidConsequenceCountermodelAt oldVisit sourceIndex
      index⟩
  everyAudit := bearerActionPaidConsequenceAuditAt
  everyFinalNoReconstruction :=
    nextPaymentOrPositiveIncidenceCannotReconstructTerminationPayment

end
end M14ProofCarryingBearerActionPaidConsequenceIndependentNecessityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBearerActionPaidConsequenceIndependentNecessityRegression.bearerActionPaidConsequenceAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBearerActionPaidConsequenceIndependentNecessityRegression.nextPaymentOrPositiveIncidenceCannotReconstructTerminationPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBearerActionPaidConsequenceIndependentNecessityRegression.proofCarryingBearerActionPaidConsequenceIndependentNecessityDirectConsumer
