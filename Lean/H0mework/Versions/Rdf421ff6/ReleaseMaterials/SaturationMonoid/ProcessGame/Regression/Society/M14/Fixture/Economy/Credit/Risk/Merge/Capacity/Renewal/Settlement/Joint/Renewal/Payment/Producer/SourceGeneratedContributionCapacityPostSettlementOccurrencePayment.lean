import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Accountability.Producer.SourceGeneratedContributionCapacityPostSettlementExternalLiability

/-!
# Post-settlement occurrence payment

The exact post-root event first generates its whole-ledger successor and its
event-selected external liability.  Only then may `NextPaidBy` project the
target occurrence from that successor.  Payment stores no next, target,
future table, row coverage, or second receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
open M14SourceGeneratedContributionCapacityBearerLeaveExecution
open M14SourceGeneratedContributionCapacityBearerRoleIndependentContinuation

abbrev PostSettlementPaymentBearerExerciseCarrierAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)) :=
  SourceGeneratedContributionCapacityBirthBearerExitAt
    (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
      index)
    (Classical.choice rootEvent.occurrence.2.periodicExitGenerated)

abbrev PostSettlementPaymentBearerExerciseResponseCarrierAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)) :=
  CanonicalContributionCapacityBearerExerciseNoncaptureResponseAt
    (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
      index)
    (Classical.choice rootEvent.occurrence.2.periodicExitGenerated)

abbrev PostSettlementPaymentBearerLeaveExecutionCarrierAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)) :=
  CanonicalContributionCapacityBearerLeaveExecutionAt
    (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
      index)
    (Classical.choice rootEvent.occurrence.2.periodicExitGenerated)

abbrev PostSettlementPaymentBearerRoleIndependentContinuationCarrierAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)) :=
  CanonicalContributionCapacityBearerRoleIndependentContinuationAt
    (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
      index)
    (Classical.choice rootEvent.occurrence.2.periodicExitGenerated)

/-- Payment at one exact post-root event.  The actual-exit witness is a type
index selected from that event's own `periodicExitGenerated`. -/
structure PostSettlementOccurrencePaymentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index))
    (actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)) : Type 18 where
  private mk ::
  write : ContributionCapacityPostSettlementExactWholeLedgerPaymentAt
    (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
      index)
  writeExact : write = PLift.up rootEvent.occurrence.2.periodicExitGenerated
  compilerWriteExact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile rootEvent.occurrence =
      .nativeWrite write
  actualExitFromWrite : actualExit = Classical.choice write.down
  exerciseFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  exerciseFaceExact : exerciseFace =
    contributionCapacityPostSettlementBirthBearerExitFaceAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  exerciseRootRead : PLift (Nonempty
    (PostSettlementPaymentBearerExerciseCarrierAt rootEvent))
  exerciseRootReadExact : exerciseRootRead =
    contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  exerciseCarrier : PostSettlementPaymentBearerExerciseCarrierAt rootEvent
  exerciseCarrierFromRootRead : exerciseCarrier =
    Classical.choice exerciseRootRead.down
  exerciseAction : birthBearerExitExerciseController.ExactActionSeed
  exerciseActionFromRootRead : exerciseAction =
    exerciseCarrier.exitExerciseAction
  exerciseControllerExact :
    birthBearerExitExerciseController.ControllerAt exerciseAction
      birthBearerWorker
  exerciseCode_eq_renewalCode :
    exerciseAction.1 = exerciseCarrier.actionableRenewal.code
  exercisePaymentOccurrenceExact :
    exerciseCarrier.existingPaymentOccurrence = actualExit.paymentOccurrence
  exerciseSettlementExact :
    exerciseCarrier.existingActualSettlement = actualExit.actualSettlement
  responseFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  responseFaceExact : responseFace =
    contributionCapacityPostSettlementBearerExerciseResponseFaceAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  responseRootRead : PLift (Nonempty
    (PostSettlementPaymentBearerExerciseResponseCarrierAt rootEvent))
  responseRootReadExact : responseRootRead =
    contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  responseCarrier :
    PostSettlementPaymentBearerExerciseResponseCarrierAt rootEvent
  responseCarrierFromRootRead : responseCarrier =
    Classical.choice responseRootRead.down
  responseAction : birthBearerExitExerciseController.ExactActionSeed
  responseActionFromRootRead : responseAction =
    responseCarrier.exerciseActionValue
  responseAction_eq_exerciseAction : responseAction = exerciseAction
  responseActionUncaptured :
    ¬ birthBearerNoCapture.Captures responseAction.1
  responseEmploymentLossExact : responseCarrier.employmentLoss =
    birthBearerEmploymentLoss
  responseEmploymentControllerExact :
    birthBearerEmploymentController.ControllerAt
      responseCarrier.employmentLoss.power.action birthBearerEmployer
  responseControllersDistinct : birthBearerEmployer ≠ birthBearerWorker
  responseActionFullCaptured :
    birthBearerFullCapture.Captures responseAction.1
  responseExactCapacity :
    (birthBearerGeometryCompilerAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)).actionableExitCapacity = 1
  responseFullCapturedCapacity :
    (birthBearerCapturedGeometryCompilerAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)).actionableExitCapacity = 0
  responsePaymentOccurrenceExact :
    responseCarrier.existingPaymentOccurrence = actualExit.paymentOccurrence
  responseSettlementExact :
    responseCarrier.existingActualSettlement = actualExit.actualSettlement
  executionFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  executionFaceExact : executionFace =
    contributionCapacityPostSettlementBearerLeaveExecutionFaceAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  executionRootRead : PLift (Nonempty
    (PostSettlementPaymentBearerLeaveExecutionCarrierAt rootEvent))
  executionRootReadExact : executionRootRead =
    contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  executionCarrier : PostSettlementPaymentBearerLeaveExecutionCarrierAt
    rootEvent
  executionCarrierFromRootRead : executionCarrier =
    Classical.choice executionRootRead.down
  executionAction : birthBearerExitExerciseController.ExactActionSeed
  executionActionFromRootRead : executionAction =
    executionCarrier.exerciseActionValue
  executionAction_eq_responseAction : executionAction = responseAction
  executionSelfActionPower : BirthBearerLeaveSelfActionPower
  executionSelfActionPowerFromRootRead : executionSelfActionPower =
    executionCarrier.selfActionPower
  executionPowerActionExact : executionSelfActionPower.action =
    executionAction
  executionSourceRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
      .source = .employed
  executionTargetRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
      .target = .released
  executionPaymentOccurrenceExact :
    executionCarrier.existingPaymentOccurrence = actualExit.paymentOccurrence
  executionSettlementExact :
    executionCarrier.existingActualSettlement = actualExit.actualSettlement
  continuationFace : SourceNativeRootSemanticFaceAt
    (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
    (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      index)
  continuationFaceExact : continuationFace =
    contributionCapacityPostSettlementBearerRoleIndependentContinuationFaceAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  continuationRootRead : PLift (Nonempty
    (PostSettlementPaymentBearerRoleIndependentContinuationCarrierAt
      rootEvent))
  continuationRootReadExact : continuationRootRead =
    contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  continuationCarrier :
    PostSettlementPaymentBearerRoleIndependentContinuationCarrierAt rootEvent
  continuationCarrierFromRootRead : continuationCarrier =
    Classical.choice continuationRootRead.down
  continuationAction : birthBearerExitExerciseController.ExactActionSeed
  continuationActionFromRootRead : continuationAction =
    continuationCarrier.exerciseActionValue
  continuationAction_eq_executionAction : continuationAction =
    executionAction
  continuationActionableExit : BirthBearerRoleIndependentActionableExit
  continuationActionableExitFromRootRead : continuationActionableExit =
    continuationCarrier.actionableExit
  continuationActionableCodeExact : continuationActionableExit.1 =
    continuationAction.1
  continuationPhaseExact :
    birthBearerExitRelationCompiler.phaseStep
      birthBearerIndependentExitRelation = 0
  continuationSourceRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
      .source = .independent
  continuationTargetRoleExact :
    birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
      .target = .independent
  continuationActionUncaptured :
    ¬ birthBearerNoCapture.Captures continuationAction.1
  continuationPaymentOccurrenceExact :
    continuationCarrier.existingPaymentOccurrence =
      actualExit.paymentOccurrence
  continuationSettlementExact :
    continuationCarrier.existingActualSettlement = actualExit.actualSettlement
  successor : SourceNativeLedgerGeneratedSuccessorAt
    rootEvent.occurrence rootEvent.wholeLedgerWriteBack
  liability : PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
    index rootEvent actualExit
  occurrenceLocalLedgerEmpty : IsEmpty
    (OpenResponsibilityAt (JointSettlementNAt oldVisit)
      rootEvent.occurrence.1)

abbrev CanonicalPostSettlementOccurrencePaymentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
    (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
      index)
    (contributionCapacityPostSettlementActualExitOfRootEventAt oldVisit
      sourceIndex index
      (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        index))

/-- Sole producer.  `PUnit.unit` is not a receipt: it is the existing
zero-information successor token whose target occurrence and ledger evolution
are already fixed by `rootEvent.wholeLedgerWriteBack`. -/
def sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex index where
  write := PLift.up
    (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
      index).occurrence.2.periodicExitGenerated
  writeExact := rfl
  compilerWriteExact := rfl
  actualExitFromWrite := rfl
  exerciseFace :=
    contributionCapacityPostSettlementBirthBearerExitFaceAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  exerciseFaceExact := rfl
  exerciseRootRead :=
    contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  exerciseRootReadExact := rfl
  exerciseCarrier := Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down
  exerciseCarrierFromRootRead := rfl
  exerciseAction := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).exitExerciseAction
  exerciseActionFromRootRead := rfl
  exerciseControllerExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).exitExerciseControllerExact
  exerciseCode_eq_renewalCode := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).exitExerciseCode_eq_renewalCode
  exercisePaymentOccurrenceExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingPaymentOccurrence_eq
  exerciseSettlementExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingActualSettlement_eq
  responseFace :=
    contributionCapacityPostSettlementBearerExerciseResponseFaceAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  responseFaceExact := rfl
  responseRootRead :=
    contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  responseRootReadExact := rfl
  responseCarrier := Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down
  responseCarrierFromRootRead := rfl
  responseAction := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).exerciseActionValue
  responseActionFromRootRead := rfl
  responseAction_eq_exerciseAction :=
    (Classical.choice
      (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
        oldVisit sourceIndex
        (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
          index)).down).exerciseActionExact |>.trans
      (Classical.choice
        (contributionCapacityPostSettlementRootGeneratedBirthBearerExitAt
          oldVisit sourceIndex
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
            index)).down).exitExerciseActionExact.symm
  responseActionUncaptured := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).actionUncaptured
  responseEmploymentLossExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).employmentLossExact
  responseEmploymentControllerExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).employmentControllerExact
  responseControllersDistinct := birthBearerEmployer_ne_birthBearerWorker
  responseActionFullCaptured := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).actionFullCaptured
  responseExactCapacity := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).exactCapacity
  responseFullCapturedCapacity := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).fullCapturedCapacity
  responsePaymentOccurrenceExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingPaymentOccurrenceExact
  responseSettlementExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingActualSettlementExact
  executionFace :=
    contributionCapacityPostSettlementBearerLeaveExecutionFaceAt oldVisit
      sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  executionFaceExact := rfl
  executionRootRead :=
    contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  executionRootReadExact := rfl
  executionCarrier := Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down
  executionCarrierFromRootRead := rfl
  executionAction := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).exerciseActionValue
  executionActionFromRootRead := rfl
  executionAction_eq_responseAction := by
    exact
      (Classical.choice
        (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
          oldVisit sourceIndex
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
            index)).down).response.exerciseActionExact |>.trans
        (Classical.choice
          (contributionCapacityPostSettlementRootGeneratedBearerExerciseResponseAt
            oldVisit sourceIndex
            (contributionCapacityPostSettlementRenewalVisitAt oldVisit
              sourceIndex index)).down).exerciseActionExact.symm
  executionSelfActionPower := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).selfActionPower
  executionSelfActionPowerFromRootRead := rfl
  executionPowerActionExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).selfActionExact
  executionSourceRoleExact :=
    birthBearerEmploymentRelation_sourceRole_exact
  executionTargetRoleExact :=
    birthBearerEmploymentRelation_targetRole_exact
  executionPaymentOccurrenceExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingPaymentOccurrenceExact
  executionSettlementExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingActualSettlementExact
  continuationFace :=
    contributionCapacityPostSettlementBearerRoleIndependentContinuationFaceAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  continuationFaceExact := rfl
  continuationRootRead :=
    contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)
  continuationRootReadExact := rfl
  continuationCarrier := Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down
  continuationCarrierFromRootRead := rfl
  continuationAction := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).exerciseActionValue
  continuationActionFromRootRead := rfl
  continuationAction_eq_executionAction := by
    exact
      (Classical.choice
        (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
          oldVisit sourceIndex
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
            index)).down).response.exerciseActionExact |>.trans
        (Classical.choice
          (contributionCapacityPostSettlementRootGeneratedBearerLeaveExecutionAt
            oldVisit sourceIndex
            (contributionCapacityPostSettlementRenewalVisitAt oldVisit
              sourceIndex index)).down).response.exerciseActionExact.symm
  continuationActionableExit := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).actionableExit
  continuationActionableExitFromRootRead := rfl
  continuationActionableCodeExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).actionableCodeExact
  continuationPhaseExact :=
    birthBearerIndependentExitRelation_phase_exact
  continuationSourceRoleExact :=
    birthBearerIndependentExitRelation_sourceRole_exact
  continuationTargetRoleExact :=
    birthBearerIndependentExitRelation_targetRole_exact
  continuationActionUncaptured := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).actionUncaptured
  continuationPaymentOccurrenceExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingPaymentOccurrenceExact
  continuationSettlementExact := (Classical.choice
    (contributionCapacityPostSettlementRootGeneratedBearerRoleIndependentContinuationAt
      oldVisit sourceIndex
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)).down).existingActualSettlementExact
  successor := PUnit.unit
  liability :=
    contributionCapacityPostSettlementGeneratedExternalLiabilityOfRootEventAt
      oldVisit sourceIndex index
      (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        index)
  occurrenceLocalLedgerEmpty := by
    rw [(contributionCapacityPostSettlementExactRootEventAt oldVisit
      sourceIndex index).occurrence.2.supportExact.down]
    exact contributionCapacityJointSettlementEmptyLedger_isEmpty oldVisit

namespace PostSettlementOccurrencePaymentAt

/-- The action/payment incidence is carried by this exact outer Payment,
rather than reconstructed from a bare opportunity or local action seed. -/
theorem bearerExercisePaidConsequence_exact
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (payment : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit) :
    payment.exerciseFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      payment.exerciseCarrier = Classical.choice payment.exerciseRootRead.down ∧
      payment.exerciseAction = payment.exerciseCarrier.exitExerciseAction ∧
      birthBearerExitExerciseController.ControllerAt payment.exerciseAction
        birthBearerWorker ∧
      payment.exerciseAction.1 = payment.exerciseCarrier.actionableRenewal.code ∧
      payment.exerciseCarrier.existingPaymentOccurrence =
        actualExit.paymentOccurrence ∧
      payment.exerciseCarrier.existingActualSettlement =
        actualExit.actualSettlement := by
  rw [payment.exerciseFaceExact]
  exact ⟨rfl, payment.exerciseCarrierFromRootRead,
    payment.exerciseActionFromRootRead, payment.exerciseControllerExact,
    payment.exerciseCode_eq_renewalCode,
    payment.exercisePaymentOccurrenceExact, payment.exerciseSettlementExact⟩

/-- The same outer Payment also reads the action-indexed noncapture response
face.  The response retains the real employment-loss action and the full-price
capture countermodel without granting either one the target leave authority. -/
theorem bearerExerciseNoncaptureResponse_exact
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (payment : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit) :
    payment.responseFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.bearerExerciseResponse ∧
      payment.responseCarrier =
        Classical.choice payment.responseRootRead.down ∧
      payment.responseAction = payment.responseCarrier.exerciseActionValue ∧
      payment.responseAction = payment.exerciseAction ∧
      ¬ birthBearerNoCapture.Captures payment.responseAction.1 ∧
      payment.responseCarrier.employmentLoss = birthBearerEmploymentLoss ∧
      birthBearerEmploymentController.ControllerAt
        payment.responseCarrier.employmentLoss.power.action
          birthBearerEmployer ∧
      birthBearerEmployer ≠ birthBearerWorker ∧
      birthBearerFullCapture.Captures payment.responseAction.1 ∧
      (birthBearerGeometryCompilerAt
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex index)).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex index)).actionableExitCapacity = 0 ∧
      payment.responseCarrier.existingPaymentOccurrence =
        actualExit.paymentOccurrence ∧
      payment.responseCarrier.existingActualSettlement =
        actualExit.actualSettlement := by
  rw [payment.responseFaceExact]
  exact ⟨rfl, payment.responseCarrierFromRootRead,
    payment.responseActionFromRootRead,
    payment.responseAction_eq_exerciseAction,
    payment.responseActionUncaptured,
    payment.responseEmploymentLossExact,
    payment.responseEmploymentControllerExact,
    payment.responseControllersDistinct,
    payment.responseActionFullCaptured,
    payment.responseExactCapacity,
    payment.responseFullCapturedCapacity,
    payment.responsePaymentOccurrenceExact,
    payment.responseSettlementExact⟩

/-- The target Payment also reads the exact bearer self-action execution face.
This is a same-occurrence typed incidence, not a claim that the action caused
the Payment or its successor. -/
theorem bearerLeaveExecution_exact
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (payment : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit) :
    payment.executionFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.bearerLeaveExecution ∧
      payment.executionCarrier =
        Classical.choice payment.executionRootRead.down ∧
      payment.executionAction =
        payment.executionCarrier.exerciseActionValue ∧
      payment.executionAction = payment.responseAction ∧
      payment.executionSelfActionPower =
        payment.executionCarrier.selfActionPower ∧
      payment.executionSelfActionPower.action = payment.executionAction ∧
      birthBearerExitExerciseController.ControllerAt payment.executionAction
        birthBearerWorker ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerEmploymentRelation ≠ 0 ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .source = .employed ∧
      birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
          .target = .released ∧
      payment.executionSelfActionPower.freedomChange =
        birthBearerEmploymentFreedomLoss ∧
      payment.executionCarrier.existingPaymentOccurrence =
        actualExit.paymentOccurrence ∧
      payment.executionCarrier.existingActualSettlement =
        actualExit.actualSettlement := by
  rw [payment.executionFaceExact]
  exact ⟨rfl, payment.executionCarrierFromRootRead,
    payment.executionActionFromRootRead,
    payment.executionAction_eq_responseAction,
    payment.executionSelfActionPowerFromRootRead,
    payment.executionPowerActionExact,
    payment.executionCarrier.controllerExact,
    payment.executionCarrier.employmentPhaseNonzero,
    payment.executionSourceRoleExact,
    payment.executionTargetRoleExact,
    (by
      rw [payment.executionSelfActionPowerFromRootRead]
      exact payment.executionCarrier.freedomChangeExact),
    payment.executionPaymentOccurrenceExact,
    payment.executionSettlementExact⟩

/-- The same Payment owns the capture-adjusted role-independent continuation
face.  Phase zero and the raw future witness are read from the continuation
carrier; this is not a second action-power claim. -/
theorem bearerRoleIndependentContinuation_exact
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (payment : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit) :
    payment.continuationFace.projection =
        ContributionCapacityPostSettlementRenewalProjection.bearerRoleIndependentContinuation ∧
      payment.continuationCarrier =
        Classical.choice payment.continuationRootRead.down ∧
      payment.continuationAction =
        payment.continuationCarrier.exerciseActionValue ∧
      payment.continuationAction = payment.executionAction ∧
      payment.continuationActionableExit =
        payment.continuationCarrier.actionableExit ∧
      payment.continuationActionableExit.1 =
        payment.continuationAction.1 ∧
      birthBearerExitRelationCompiler.phaseStep
          birthBearerIndependentExitRelation = 0 ∧
      birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
          .source = .independent ∧
      birthBearerExitRelationCompiler.roleAt birthBearerIndependentExitRelation
          .target = .independent ∧
      Nonempty
        (birthBearerExitRelationCompiler.FutureContinuationAt
          birthBearerIndependentExitRelation.1 .target
            payment.continuationAction.1) ∧
      ¬ birthBearerNoCapture.Captures payment.continuationAction.1 ∧
      payment.continuationCarrier.existingPaymentOccurrence =
        actualExit.paymentOccurrence ∧
      payment.continuationCarrier.existingActualSettlement =
        actualExit.actualSettlement := by
  rw [payment.continuationFaceExact]
  exact
    ⟨rfl, payment.continuationCarrierFromRootRead,
      payment.continuationActionFromRootRead,
      payment.continuationAction_eq_executionAction,
      payment.continuationActionableExitFromRootRead,
      payment.continuationActionableCodeExact,
      payment.continuationPhaseExact,
      payment.continuationSourceRoleExact,
      payment.continuationTargetRoleExact,
      (by
        rw [payment.continuationActionFromRootRead]
        exact ⟨payment.continuationCarrier.futureContinuation⟩),
      payment.continuationActionUncaptured,
      payment.continuationPaymentOccurrenceExact,
      payment.continuationSettlementExact⟩

/-- Complete row disposition is derived from the indexed whole-ledger image.
At the post-settlement empty fibre its domain is empty, while `liability`
remains nonempty and prevents that vacuity from erasing external payment. -/
def dispositionAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (payment : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit) :=
  fun entry =>
    LedgerEntryDispositionAt.evolved
      (payment.successor.ledgerEvolution.destination entry).2

/-- The paid next is a projection of the payment's compiler-generated
successor, never a field or constructor argument. -/
def nextPaidBy
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (payment : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit) :=
  payment.successor.targetOccurrence

@[simp] theorem nextPaidBy_current_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index).successor.targetCurrent =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
          index +
        1 :=
  rfl

@[simp] theorem nextPaidBy_occurrence_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex index).nextPaidBy =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
            sourceIndex index +
          1) :=
  rfl

end PostSettlementOccurrencePaymentAt

end
end M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt.bearerExercisePaidConsequence_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt.bearerExerciseNoncaptureResponse_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt.bearerLeaveExecution_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt.bearerRoleIndependentContinuation_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt.nextPaidBy_occurrence_exact
