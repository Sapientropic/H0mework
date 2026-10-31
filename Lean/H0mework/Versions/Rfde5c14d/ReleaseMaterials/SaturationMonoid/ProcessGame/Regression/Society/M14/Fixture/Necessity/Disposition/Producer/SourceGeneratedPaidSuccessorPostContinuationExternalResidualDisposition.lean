import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Continuation.Producer.SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation

/-!
# Post-continuation external residual disposition

The successor Payment that owns the role-independent continuation also owns
an event-selected external liability.  This carrier consumes that existing
liability together with its source ownership, independent root consumer,
exact settlement, actionable renewal and root factorization.  The local
ledger is empty but its whole-ledger disposition remains total; that vacuity
cannot erase the external responsibility.

No action receipt, liability ledger, residual registry or local row is added.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation

/-- The exact external-residual disposition generated from an already
certified continuation. -/
structure PostContinuationExternalResidualDispositionAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (continuation :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) : Type 30 where
  private mk ::
  liability : PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
    (index + 1 + 1) continuation.successorRootEvent
      continuation.paidContinuationStep.targetCurrent.actualExit
  liabilityExact : liability = continuation.successorPayment.liability
  sourceOwnedResidual :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership
  sourceOwnedResidualExact : sourceOwnedResidual =
    liability.sourceOwnedResidual
  rootConsumer : Nonempty
    (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      continuation.paidContinuationStep.targetCurrent.actualExit)
  rootConsumerExact : rootConsumer = liability.rootConsumer
  exactSettlement : Nonempty
    { settlement : ExactServedCrossingDebitedRunAt
        (anomiePhaseAt
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
            sourceIndex (index + 1 + 1)))
        debited
        (serviceCompilerAt
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
            sourceIndex (index + 1 + 1))) //
      settlement =
        continuation.paidContinuationStep.targetCurrent.actualExit.actualSettlement }
  exactSettlementExact : exactSettlement = liability.actualSettlement
  actionableRenewal : Nonempty
    { renewal :
        (geometryCompilerAt
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
            sourceIndex (index + 1 + 1))).SourceGeneratedActionableExitRenewalAt //
      renewal =
        continuation.paidContinuationStep.targetCurrent.actualExit.actionableRenewal }
  actionableRenewalExact : actionableRenewal = liability.actionableRenewal
  rootFactorization :
    continuation.paidContinuationStep.targetCurrent.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes
  rootFactorizationExact : rootFactorization = liability.rootFactorization
  localLedgerEmpty : IsEmpty
    (OpenResponsibilityAt (JointSettlementNAt oldVisit)
      continuation.successorRootEvent.occurrence.1)
  localDisposition :
    (entry : OpenResponsibilityAt (JointSettlementNAt oldVisit)
      continuation.successorRootEvent.occurrence.1) →
      LedgerEntryDispositionAt (JointSettlementNAt oldVisit) entry
  wholeLedgerSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    continuation.successorRootEvent.occurrence
    continuation.successorRootEvent.wholeLedgerWriteBack
  wholeLedgerSuccessorExact : wholeLedgerSuccessor =
    continuation.successorPayment.successor

abbrev CanonicalPostContinuationExternalResidualDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  PostContinuationExternalResidualDispositionAt
    (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index)

def sourceGeneratedPaidSuccessorPostContinuationExternalResidualDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPostContinuationExternalResidualDispositionAt oldVisit
      sourceIndex index := by
  let continuation :=
    sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index
  let liability := continuation.successorPayment.liability
  exact
    { liability := liability
      liabilityExact := rfl
      sourceOwnedResidual := liability.sourceOwnedResidual
      sourceOwnedResidualExact := rfl
      rootConsumer := liability.rootConsumer
      rootConsumerExact := rfl
      exactSettlement := liability.actualSettlement
      exactSettlementExact := rfl
      actionableRenewal := liability.actionableRenewal
      actionableRenewalExact := rfl
      rootFactorization := liability.rootFactorization
      rootFactorizationExact := rfl
      localLedgerEmpty :=
        continuation.successorPayment.occurrenceLocalLedgerEmpty
      localDisposition :=
        continuation.successorPayment.dispositionAt
      wholeLedgerSuccessor := continuation.successorPayment.successor
      wholeLedgerSuccessorExact := rfl }

/-- A substantive local disposition requires an actual local entry.  This is
distinct from the total function on an empty entry fibre. -/
abbrev PostContinuationLocalDispositionWitnessAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (continuation :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) :=
  Sigma fun entry : OpenResponsibilityAt (JointSettlementNAt oldVisit)
      continuation.successorRootEvent.occurrence.1 =>
    LedgerEntryDispositionAt (JointSettlementNAt oldVisit) entry

def PostContinuationExternalCrossRootDistinctAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (continuation :
      SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index) : Prop :=
  Sum.inl continuation.successorRootEvent ≠
    Sum.inr
      continuation.paidContinuationStep.targetCurrent.actualExit.paymentOccurrence.rootOccurrence

namespace PostContinuationExternalResidualDispositionAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  {continuation :
    SourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index}
  (disposition : PostContinuationExternalResidualDispositionAt continuation)

include disposition

/-- Action/future and liability are both owned by the exact same successor
Payment occurrence and its event-selected actual exit. -/
theorem sameSuccessorPaymentActionAndLiability :
    continuation.successorContinuationCarrier =
        Classical.choice continuation.successorContinuationRootRead.down ∧
      continuation.successorContinuationAction =
        continuation.successorContinuationCarrier.exerciseActionValue ∧
      continuation.successorContinuationCarrier.existingPaymentOccurrence =
        continuation.paidContinuationStep.targetCurrent.actualExit.paymentOccurrence ∧
      continuation.successorContinuationCarrier.existingActualSettlement =
        continuation.paidContinuationStep.targetCurrent.actualExit.actualSettlement ∧
      disposition.liability = continuation.successorPayment.liability ∧
      disposition.liability.paymentInstalledExact =
        continuation.successorPayment.liability.paymentInstalledExact :=
  ⟨continuation.successorPayment.continuationCarrierFromRootRead,
    continuation.successorPayment.continuationActionFromRootRead,
    continuation.successorPayment.continuationPaymentOccurrenceExact,
    continuation.successorPayment.continuationSettlementExact,
    disposition.liabilityExact,
    congrArg PostSettlementGeneratedExternalLiabilityAt.paymentInstalledExact
      disposition.liabilityExact⟩

omit disposition in
theorem successorCompilerWriteExact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        continuation.successorRootEvent.occurrence =
      .nativeWrite continuation.successorPayment.write :=
  continuation.paidContinuationStep.targetCompilerWrite_exact

omit disposition in
theorem successorActualExitFromWriteExact :
    continuation.paidContinuationStep.targetCurrent.actualExit =
      Classical.choice continuation.successorPayment.write.down :=
  continuation.successorPayment.actualExitFromWrite

theorem liabilityCrossRootOccurrenceDistinct :
    PostContinuationExternalCrossRootDistinctAt continuation :=
  disposition.liability.crossRootOccurrenceDistinct

def localWholeLedgerDispositionTotal :
    (entry : OpenResponsibilityAt (JointSettlementNAt oldVisit)
      continuation.successorRootEvent.occurrence.1) →
      LedgerEntryDispositionAt (JointSettlementNAt oldVisit) entry :=
  disposition.localDisposition

theorem substantiveLocalDisposition_isEmpty :
    IsEmpty (PostContinuationLocalDispositionWitnessAt continuation) :=
  ⟨fun witness => disposition.localLedgerEmpty.false witness.1⟩

/-- Empty substantive local disposition coexists with the exact external
liability; the total empty-domain function is not external responsibility. -/
theorem substantiveLocalDispositionEmpty_externalLiabilityNonempty :
    IsEmpty (PostContinuationLocalDispositionWitnessAt continuation) ∧
      Nonempty
        (PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
          (index + 1 + 1) continuation.successorRootEvent
            continuation.paidContinuationStep.targetCurrent.actualExit) :=
  ⟨disposition.substantiveLocalDisposition_isEmpty,
    ⟨disposition.liability⟩⟩

/-- This exact local empty fibre cannot erase the existing external
liability. -/
theorem localEmpty_doesNotEraseExactExternalLiability :
    ¬ (IsEmpty
          (OpenResponsibilityAt (JointSettlementNAt oldVisit)
            continuation.successorRootEvent.occurrence.1) →
        ¬ PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
          (index + 1 + 1) continuation.successorRootEvent
            continuation.paidContinuationStep.targetCurrent.actualExit) := by
  intro erases
  exact erases disposition.localLedgerEmpty disposition.liability

omit disposition in
/-- Direct specialization of the existing post-root no-erasure theorem at
the continuation successor current. -/
theorem installedExternalAuthorityNoErasure :
    ¬ (IsEmpty
          (OpenResponsibilityAt (JointSettlementNAt oldVisit)
            continuation.successorRootEvent.occurrence.1) →
        ¬ ContributionCapacityPostSettlementExternalPaymentAuthorityAt
          oldVisit sourceIndex (index + 1 + 1)
            continuation.successorRootEvent) := by
  simpa using
    (contributionCapacityPostSettlementEmptyLedger_doesNotEraseExternalLiability
      oldVisit sourceIndex (index + 1 + 1))

def furtherPaidStep
    (_disposition : PostContinuationExternalResidualDispositionAt
      continuation) :=
  continuation.paidContinuationStep.generatedNextPaidStep

theorem furtherPaidStep_sourcePaymentExact :
    disposition.furtherPaidStep.sourcePayment =
      continuation.successorPayment :=
  rfl

theorem furtherPaidNext_isExactOuterOccurrence :
    HEq continuation.successorPayment.nextPaidBy
      disposition.furtherPaidStep.targetRootEvent.occurrence := by
  rw [← disposition.furtherPaidStep_sourcePaymentExact]
  exact disposition.furtherPaidStep.nextPaidBy_isTargetCanonicalOccurrence

theorem servicesExternalSuccessorAndFurtherNextRemain :
    (∀ channel : EssentialAccessChannel,
      Nonempty
        (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex (index + 1 + 1) channel)) ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          continuation.paidContinuationStep.targetCurrent.actualExit) ∧
      disposition.wholeLedgerSuccessor =
        continuation.successorPayment.successor ∧
      HEq continuation.successorPayment.nextPaidBy
        disposition.furtherPaidStep.targetRootEvent.occurrence ∧
      continuation.successorPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
              sourceIndex (index + 1 + 1) +
            1) := by
  have external :=
    continuation.successorExternalConsumerSuccessorAndFurtherNext
  exact
    ⟨fun channel =>
        (continuation.everySuccessorChannelServiceAndNext channel).1,
      disposition.sourceOwnedResidual,
      disposition.rootConsumer,
      disposition.wholeLedgerSuccessorExact,
      disposition.furtherPaidNext_isExactOuterOccurrence,
      external.2.2.2⟩

/-- Main post-continuation external-residual seal. -/
theorem postContinuationExternalResidualDisposition_exact :
    continuation.successorContinuationAction =
        continuation.execution.targetExecutionAction ∧
      disposition.liability = continuation.successorPayment.liability ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          continuation.paidContinuationStep.targetCurrent.actualExit) ∧
      continuation.paidContinuationStep.targetCurrent.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes ∧
      IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          continuation.successorRootEvent.occurrence.1) ∧
      Nonempty
        ((entry : OpenResponsibilityAt (JointSettlementNAt oldVisit)
            continuation.successorRootEvent.occurrence.1) →
          LedgerEntryDispositionAt (JointSettlementNAt oldVisit) entry) ∧
      disposition.wholeLedgerSuccessor =
        continuation.successorPayment.successor :=
  ⟨continuation.successorAction_eq_executedAction,
    disposition.liabilityExact,
    disposition.sourceOwnedResidual,
    disposition.rootConsumer,
    disposition.rootFactorization,
    disposition.localLedgerEmpty,
    ⟨disposition.localDisposition⟩,
    disposition.wholeLedgerSuccessorExact⟩

end PostContinuationExternalResidualDispositionAt

/-! ## Exact deletion controls -/

structure ExactPostContinuationSourceOwnershipDeletionAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (disposition : CanonicalPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index) : Type 31 where
  sourceOwnershipDeleted :
    IsEmpty ContributionCapacityPostSettlementPaymentSourceOwnership

theorem sourceOwnershipDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (disposition : CanonicalPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index) :
    IsEmpty (ExactPostContinuationSourceOwnershipDeletionAt disposition) :=
  ⟨fun deletion =>
    deletion.sourceOwnershipDeleted.false
      (Classical.choice disposition.sourceOwnedResidual)⟩

structure ExactPostContinuationRootConsumerDeletionAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (disposition : CanonicalPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index) : Type 31 where
  rootConsumerDeleted : IsEmpty
    (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index).paidContinuationStep.targetCurrent.actualExit)

theorem rootConsumerDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (disposition : CanonicalPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index) :
    IsEmpty (ExactPostContinuationRootConsumerDeletionAt disposition) :=
  ⟨fun deletion =>
    deletion.rootConsumerDeleted.false
      (Classical.choice disposition.rootConsumer)⟩

structure ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (disposition : CanonicalPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index) : Type 31 where
  localEmpty : IsEmpty
    (OpenResponsibilityAt (JointSettlementNAt oldVisit)
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index).successorRootEvent.occurrence.1)
  externalLiabilityDeleted :
    ¬ PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
      (index + 1 + 1)
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index).successorRootEvent
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index).paidContinuationStep.targetCurrent.actualExit

theorem localEmptyErasesExternalLiability_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (disposition : CanonicalPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index) :
    IsEmpty
      (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
        disposition) :=
  ⟨fun erasure => erasure.externalLiabilityDeleted disposition.liability⟩

theorem postContinuationExternalResidualDisposition_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let disposition :=
    sourceGeneratedPaidSuccessorPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index
  fail_if_success exact disposition.action
  fail_if_success exact disposition.payment
  fail_if_success exact disposition.consumer
  fail_if_success exact disposition.owner
  fail_if_success exact disposition.entry
  fail_if_success exact disposition.target
  fail_if_success exact disposition.registry
  fail_if_success exact disposition.future
  trivial

end
end M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition.sourceGeneratedPaidSuccessorPostContinuationExternalResidualDispositionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition.PostContinuationExternalResidualDispositionAt.postContinuationExternalResidualDisposition_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition.sourceOwnershipDeletion_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition.rootConsumerDeletion_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition.localEmptyErasesExternalLiability_isEmpty
