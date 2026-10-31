import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Exercise.Producer.SourceGeneratedBearerOwnedExitExerciseIndependentNecessity

/-!
# Independent necessity of bearer-action / paid-consequence alignment

The exact post-settlement Payment now reads its `.birthBearerExit` face and
carries that root-read's `.t1/.leave` action beside the native write-selected
actual exit, external liability and successor.  This file packages that typed
incidence and contrasts it with the real `.t0` employment-termination action.

The three occurrence layers remain distinct: outer post-root authority,
embedded M9 Payment, and fixed local action trace.  The producer accepts only
the existing root indices; it accepts no action, Payment, receipt, consequence,
target or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity

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

abbrev CanonicalBearerActionPostPaymentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex index

def canonicalBearerActionPostPaymentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalBearerActionPostPaymentAt oldVisit sourceIndex index :=
  sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
    oldVisit sourceIndex index

/-! ## Positive typed action-payment incidence -/

structure ExactBearerActionPaidConsequenceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 25 where
  private mk ::
  outerRootEvent : ExactTemporalCausalRootEventAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  outerRootEventExact : outerRootEvent =
    contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
      index
  payment : CanonicalBearerActionPostPaymentAt oldVisit sourceIndex index
  paymentExact : payment =
    canonicalBearerActionPostPaymentAt oldVisit sourceIndex index
  nativeWrite : ContributionCapacityPostSettlementExactWholeLedgerPaymentAt
    (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
      index)
  nativeWriteFromPayment : nativeWrite = payment.write
  nativeWriteFromOuterEvent : nativeWrite =
    PLift.up outerRootEvent.occurrence.2.periodicExitGenerated
  actualExit : PeriodicActualServiceExitAt
    (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
      index)
  actualExitExact : actualExit = Classical.choice nativeWrite.down
  exerciseFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  exerciseFaceFromPayment : exerciseFace = payment.exerciseFace
  exerciseRootRead : PLift (Nonempty
    (PostSettlementPaymentBearerExerciseCarrierAt outerRootEvent))
  exerciseRootReadFromPayment : HEq exerciseRootRead payment.exerciseRootRead
  exerciseCarrier : PostSettlementPaymentBearerExerciseCarrierAt outerRootEvent
  exerciseCarrierFromRootRead : exerciseCarrier =
    Classical.choice exerciseRootRead.down
  exerciseCarrierFromPayment : HEq exerciseCarrier payment.exerciseCarrier
  exerciseAction : birthBearerExitExerciseController.ExactActionSeed
  exerciseActionFromCarrier : exerciseAction =
    exerciseCarrier.exitExerciseAction
  exerciseActionFromPayment : exerciseAction = payment.exerciseAction
  exerciseControllerExact :
    birthBearerExitExerciseController.ControllerAt exerciseAction
      birthBearerWorker
  exerciseCode_eq_renewalCode :
    exerciseAction.1 = exerciseCarrier.actionableRenewal.code
  exerciseCode_eq_leave : exerciseAction.1 = ExitFutureCode.leave
  exerciseSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt exerciseAction.1
  exercisePaymentOccurrenceExact :
    exerciseCarrier.existingPaymentOccurrence = actualExit.paymentOccurrence
  exerciseSettlementExact :
    exerciseCarrier.existingActualSettlement = actualExit.actualSettlement
  externalLiability : PostSettlementGeneratedExternalLiabilityAt oldVisit
    sourceIndex index outerRootEvent actualExit
  externalLiabilityFromPayment : HEq externalLiability payment.liability
  externalSourceOwnership :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership
  externalRootConsumer : Nonempty
    (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt actualExit)
  successor : SourceNativeLedgerGeneratedSuccessorAt
    outerRootEvent.occurrence outerRootEvent.wholeLedgerWriteBack
  successorFromPayment : HEq successor payment.successor
  nextPaidByExact : payment.nextPaidBy =
    contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index + 1)
  localLedgerEmpty : IsEmpty
    (OpenResponsibilityAt (JointSettlementNAt oldVisit)
      outerRootEvent.occurrence.1)
  outerEmbeddedDistinct :
    (Sum.inl outerRootEvent :
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
      Sum.inr actualExit.paymentOccurrence.rootOccurrence

/-- Sole producer from one exact existing post-root event. -/
def exactBearerActionPaidConsequenceAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ExactBearerActionPaidConsequenceAt oldVisit sourceIndex index := by
  let outerRootEvent :=
    contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
      index
  let payment :=
    canonicalBearerActionPostPaymentAt oldVisit sourceIndex index
  let nativeWrite := payment.write
  let actualExit := Classical.choice nativeWrite.down
  let exerciseRootRead := payment.exerciseRootRead
  let exerciseCarrier := Classical.choice exerciseRootRead.down
  let exerciseAction := exerciseCarrier.exitExerciseAction
  exact
    { outerRootEvent := outerRootEvent
      outerRootEventExact := rfl
      payment := payment
      paymentExact := rfl
      nativeWrite := nativeWrite
      nativeWriteFromPayment := rfl
      nativeWriteFromOuterEvent := payment.writeExact
      actualExit := actualExit
      actualExitExact := rfl
      exerciseFace := payment.exerciseFace
      exerciseFaceFromPayment := rfl
      exerciseRootRead := exerciseRootRead
      exerciseRootReadFromPayment := HEq.rfl
      exerciseCarrier := exerciseCarrier
      exerciseCarrierFromRootRead := rfl
      exerciseCarrierFromPayment := HEq.rfl
      exerciseAction := exerciseAction
      exerciseActionFromCarrier := rfl
      exerciseActionFromPayment := rfl
      exerciseControllerExact := exerciseCarrier.exitExerciseControllerExact
      exerciseCode_eq_renewalCode :=
        exerciseCarrier.exitExerciseCode_eq_renewalCode
      exerciseCode_eq_leave := by
        change exerciseCarrier.exitExerciseAction.1 = ExitFutureCode.leave
        rw [exerciseCarrier.exitExerciseActionExact]
        rfl
      exerciseSourceTrace := exerciseCarrier.exitExerciseSourceProvenance
      exercisePaymentOccurrenceExact :=
        payment.exercisePaymentOccurrenceExact
      exerciseSettlementExact := payment.exerciseSettlementExact
      externalLiability := payment.liability
      externalLiabilityFromPayment := HEq.rfl
      externalSourceOwnership := payment.liability.sourceOwnedResidual
      externalRootConsumer := payment.liability.rootConsumer
      successor := payment.successor
      successorFromPayment := HEq.rfl
      nextPaidByExact := rfl
      localLedgerEmpty := payment.occurrenceLocalLedgerEmpty
      outerEmbeddedDistinct := payment.liability.crossRootOccurrenceDistinct }

/-! ## Real termination action cannot be the paid bearer leave -/

structure ExactEmploymentTerminationPaidAsBearerLeaveAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 25 where
  private mk ::
  paidConsequence : ExactBearerActionPaidConsequenceAt oldVisit sourceIndex
    index
  terminationAction : birthBearerEmploymentController.ExactActionSeed
  terminationActionExact : terminationAction =
    birthBearerExactEmploymentAction
  terminationControllerExact :
    birthBearerEmploymentController.ControllerAt terminationAction
      birthBearerEmployer
  terminationSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerEmploymentController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerEmploymentController.actionAdmittedAt terminationAction.1
  paymentExerciseController_eq_terminationController :
    birthBearerWorker = birthBearerEmployer

theorem employmentTerminationPaidAsBearerLeave_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty (ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit
      sourceIndex index) :=
  ⟨fun falsePayment =>
    birthBearerEmployer_ne_birthBearerWorker
      falsePayment.paymentExerciseController_eq_terminationController.symm⟩

/-! ## Full countermodel and controls -/

structure SourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 26 where
  private mk ::
  paidConsequence : ExactBearerActionPaidConsequenceAt oldVisit sourceIndex
    index
  paidConsequenceExact : paidConsequence =
    exactBearerActionPaidConsequenceAt oldVisit sourceIndex index
  priorExercise :
    SourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
      sourceIndex index
  priorExerciseExact : priorExercise =
    sourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
      sourceIndex index
  realTerminationAction : birthBearerEmploymentController.ExactActionSeed
  realTerminationActionExact : realTerminationAction =
    birthBearerExactEmploymentAction
  realTerminationControllerExact :
    birthBearerEmploymentController.ControllerAt realTerminationAction
      birthBearerEmployer
  terminationPaymentDeleted : IsEmpty
    (ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit sourceIndex index)

def sourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt oldVisit
      sourceIndex index where
  paidConsequence :=
    exactBearerActionPaidConsequenceAt oldVisit sourceIndex index
  paidConsequenceExact := rfl
  priorExercise :=
    sourceGeneratedBearerOwnedExitExerciseIndependentNecessityAt oldVisit
      sourceIndex index
  priorExerciseExact := rfl
  realTerminationAction := birthBearerExactEmploymentAction
  realTerminationActionExact := rfl
  realTerminationControllerExact := rfl
  terminationPaymentDeleted :=
    employmentTerminationPaidAsBearerLeave_isEmpty oldVisit sourceIndex index

namespace SourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (countermodel :
    SourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt oldVisit
      sourceIndex index)

include countermodel

theorem actionWriteLiabilityAndNextCommute :
    countermodel.paidConsequence.exerciseFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      countermodel.paidConsequence.exerciseCarrier =
        Classical.choice countermodel.paidConsequence.exerciseRootRead.down ∧
      countermodel.paidConsequence.exerciseAction =
        countermodel.paidConsequence.exerciseCarrier.exitExerciseAction ∧
      countermodel.paidConsequence.exerciseAction =
        countermodel.paidConsequence.payment.exerciseAction ∧
      countermodel.paidConsequence.actualExit =
        Classical.choice countermodel.paidConsequence.nativeWrite.down ∧
      countermodel.paidConsequence.exerciseCarrier.existingPaymentOccurrence =
        countermodel.paidConsequence.actualExit.paymentOccurrence ∧
      countermodel.paidConsequence.exerciseCarrier.existingActualSettlement =
        countermodel.paidConsequence.actualExit.actualSettlement ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        countermodel.paidConsequence.actualExit) ∧
      countermodel.paidConsequence.payment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
            sourceIndex index + 1) := by
  rw [countermodel.paidConsequence.exerciseFaceFromPayment]
  have paid := countermodel.paidConsequence.payment
    |>.bearerExercisePaidConsequence_exact
  exact ⟨paid.1,
    countermodel.paidConsequence.exerciseCarrierFromRootRead,
    countermodel.paidConsequence.exerciseActionFromCarrier,
    countermodel.paidConsequence.exerciseActionFromPayment,
    countermodel.paidConsequence.actualExitExact,
    countermodel.paidConsequence.exercisePaymentOccurrenceExact,
    countermodel.paidConsequence.exerciseSettlementExact,
    countermodel.paidConsequence.externalSourceOwnership,
    countermodel.paidConsequence.externalRootConsumer,
    countermodel.paidConsequence.nextPaidByExact⟩

theorem realTerminationAndAllNonTargetAxesRemain :
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
        index) ∧
      IsEmpty (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        countermodel.paidConsequence.outerRootEvent.occurrence.1) ∧
      IsEmpty (ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit
        sourceIndex index) :=
  let prior := countermodel.priorExercise
  ⟨countermodel.realTerminationControllerExact,
    ⟨prior.positiveExercise.opportunity⟩,
    ⟨prior.positiveExercise.actionableRenewal⟩,
    prior.positiveExercise.bearerExit.exactCapacity,
    ⟨prior.positiveExercise.tenureAlignment⟩,
    countermodel.paidConsequence.localLedgerEmpty,
    countermodel.terminationPaymentDeleted⟩

end SourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt

theorem bareActionCannotReconstructTerminationPayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (birthBearerExitExerciseController.ExactActionSeed →
        ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit sourceIndex
          index) :=
  let deleted :=
    employmentTerminationPaidAsBearerLeave_isEmpty oldVisit sourceIndex index
  ⟨fun reconstruct => deleted.false
    (reconstruct birthBearerExactExitExerciseAction)⟩

theorem paymentReceiptCannotReconstructTerminationPayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (SourceBackedUBIPaymentReceiptAt
          birthBearerExitCapacityProgram.purchasingPowerStanding
          ExitFutureCode.leave →
        ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit sourceIndex
          index) :=
  let deleted :=
    employmentTerminationPaidAsBearerLeave_isEmpty oldVisit sourceIndex index
  ⟨fun reconstruct => deleted.false
    (reconstruct birthBearerPaymentReceipt)⟩

theorem actualExitCannotReconstructTerminationPayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (PeriodicActualServiceExitAt
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
            sourceIndex index) →
        ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit sourceIndex
          index) :=
  let deleted :=
    employmentTerminationPaidAsBearerLeave_isEmpty oldVisit sourceIndex index
  let positive :=
    exactBearerActionPaidConsequenceAt oldVisit sourceIndex index
  ⟨fun reconstruct => deleted.false (reconstruct positive.actualExit)⟩

theorem liabilityCannotReconstructTerminationPayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let positive :=
      exactBearerActionPaidConsequenceAt oldVisit sourceIndex index
    IsEmpty
      (PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex index
          positive.outerRootEvent positive.actualExit →
        ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit sourceIndex
          index) := by
  let positive :=
    exactBearerActionPaidConsequenceAt oldVisit sourceIndex index
  let deleted :=
    employmentTerminationPaidAsBearerLeave_isEmpty oldVisit sourceIndex index
  exact ⟨fun reconstruct => deleted.false
    (reconstruct positive.externalLiability)⟩

theorem fullCarrierCannotReconstructTerminationPayment
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (SourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt
          oldVisit sourceIndex index →
        ExactEmploymentTerminationPaidAsBearerLeaveAt oldVisit sourceIndex
          index) :=
  let deleted :=
    employmentTerminationPaidAsBearerLeave_isEmpty oldVisit sourceIndex index
  ⟨fun reconstruct => deleted.false
    (reconstruct
      (sourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt
        oldVisit sourceIndex index))⟩

theorem bearerActionPaidConsequenceProducer_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let generated :=
    sourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt oldVisit
      sourceIndex index
  fail_if_success exact generated.action
  fail_if_success exact generated.payment
  fail_if_success exact generated.receipt
  fail_if_success exact generated.consequence
  fail_if_success exact generated.target
  fail_if_success exact generated.future
  fail_if_success exact generated.registry
  trivial

end
end M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity.exactBearerActionPaidConsequenceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity.sourceGeneratedBearerActionPaidConsequenceIndependentNecessityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity.fullCarrierCannotReconstructTerminationPayment
