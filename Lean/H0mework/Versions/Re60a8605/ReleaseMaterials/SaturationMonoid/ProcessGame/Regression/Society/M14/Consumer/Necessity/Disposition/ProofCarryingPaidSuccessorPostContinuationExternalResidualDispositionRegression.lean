import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Disposition.Producer.SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Continuation.ProofCarryingPaidSuccessorBearerRoleIndependentContinuationRegression

/-!
# Direct consumer of post-continuation external residual disposition

The audit consumes the successor Payment's continuation incidence and its
event-selected liability as one typed package.  It checks source ownership,
independent root consumption, settlement, actionable renewal, root
factorization, total local disposition, external no-erasure, services,
whole-ledger successor and further paid next.  Deleting source ownership,
the root consumer or the external liability is constructively impossible.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
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
open M14ProofCarryingPaidSuccessorBearerRoleIndependentContinuationRegression
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition

abbrev CanonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  CanonicalPostContinuationExternalResidualDispositionAt oldVisit sourceIndex
    index

def canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index :=
  sourceGeneratedPaidSuccessorPostContinuationExternalResidualDispositionAt
    oldVisit sourceIndex index

structure PaidSuccessorPostContinuationExternalResidualDispositionAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (disposition :
      CanonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
        oldVisit sourceIndex index) : Prop where
  canonicalExact : disposition =
    canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index
  priorContinuationAudit :
    PaidSuccessorBearerRoleIndependentContinuationAuditAt
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
        oldVisit sourceIndex index)
  sameSuccessorPaymentActionAndLiability :
    (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
          sourceIndex index).successorContinuationCarrier =
        Classical.choice
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index).successorContinuationRootRead.down ∧
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
          sourceIndex index).successorContinuationAction =
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).successorContinuationCarrier.exerciseActionValue ∧
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
          sourceIndex index).successorContinuationCarrier.existingPaymentOccurrence =
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit.paymentOccurrence ∧
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
          sourceIndex index).successorContinuationCarrier.existingActualSettlement =
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit.actualSettlement ∧
      disposition.liability =
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).successorPayment.liability
  successorCompilerWriteAndActualExitExact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).successorRootEvent.occurrence =
      .nativeWrite
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).successorPayment.write ∧
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
          sourceIndex index).paidContinuationStep.targetCurrent.actualExit =
        Classical.choice
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index).successorPayment.write.down
  liabilityCrossRootOccurrenceDistinct :
    PostContinuationExternalCrossRootDistinctAt
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
        oldVisit sourceIndex index)
  liabilitySourceProvenance :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      residualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        (PurchasingPowerStandingAt.renewalEvent
          exitCapacityProgram.purchasingPowerStanding)
  externalResponsibility :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit) ∧
      Nonempty
        { settlement : ExactServedCrossingDebitedRunAt
            (anomiePhaseAt
              (contributionCapacityPostSettlementReachableCurrentAt oldVisit
                sourceIndex (index + 1 + 1)))
            debited
            (serviceCompilerAt
              (contributionCapacityPostSettlementReachableCurrentAt oldVisit
                sourceIndex (index + 1 + 1))) //
          settlement =
            (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
              oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit.actualSettlement } ∧
      Nonempty
        { renewal :
            (geometryCompilerAt
              (contributionCapacityPostSettlementReachableCurrentAt oldVisit
                sourceIndex (index + 1 + 1))).SourceGeneratedActionableExitRenewalAt //
          renewal =
            (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
              oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit.actionableRenewal } ∧
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index).paidContinuationStep.targetCurrent.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes
  localDispositionAndExactNoErasure :
    IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index).successorRootEvent.occurrence.1) ∧
      Nonempty
        ((entry : OpenResponsibilityAt (JointSettlementNAt oldVisit)
            (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
              oldVisit sourceIndex index).successorRootEvent.occurrence.1) →
          LedgerEntryDispositionAt (JointSettlementNAt oldVisit) entry) ∧
      ¬ (IsEmpty
            (OpenResponsibilityAt (JointSettlementNAt oldVisit)
              (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
                oldVisit sourceIndex index).successorRootEvent.occurrence.1) →
          ¬ PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
            (index + 1 + 1)
            (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
              oldVisit sourceIndex index).successorRootEvent
            (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
              oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit)
  substantiveLocalEmptyButExternalNonempty :
    IsEmpty
        (PostContinuationLocalDispositionWitnessAt
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index)) ∧
      Nonempty
        (PostSettlementGeneratedExternalLiabilityAt oldVisit sourceIndex
          (index + 1 + 1)
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index).successorRootEvent
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit)
  installedExternalAuthorityNoErasure :
    ¬ (IsEmpty
          (OpenResponsibilityAt (JointSettlementNAt oldVisit)
            (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
              oldVisit sourceIndex index).successorRootEvent.occurrence.1) →
        ¬ ContributionCapacityPostSettlementExternalPaymentAuthorityAt
          oldVisit sourceIndex (index + 1 + 1)
            (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
              oldVisit sourceIndex index).successorRootEvent)
  servicesExternalSuccessorAndFurtherNext :
    (∀ channel : EssentialAccessChannel,
      Nonempty
        (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex (index + 1 + 1) channel)) ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
            oldVisit sourceIndex index).paidContinuationStep.targetCurrent.actualExit) ∧
      disposition.wholeLedgerSuccessor =
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).successorPayment.successor ∧
      HEq
        (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt
          oldVisit sourceIndex index).successorPayment.nextPaidBy
        disposition.furtherPaidStep.targetRootEvent.occurrence ∧
      (sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
        sourceIndex index).successorPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (contributionCapacityPostSettlementReachableCurrentAt oldVisit
              sourceIndex (index + 1 + 1) +
            1)
  sourceOwnershipDeletionEmpty : IsEmpty
    (ExactPostContinuationSourceOwnershipDeletionAt disposition)
  rootConsumerDeletionEmpty : IsEmpty
    (ExactPostContinuationRootConsumerDeletionAt disposition)
  localEmptyErasureEmpty : IsEmpty
    (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt disposition)

theorem paidSuccessorPostContinuationExternalResidualDispositionAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidSuccessorPostContinuationExternalResidualDispositionAuditAt
      (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
        oldVisit sourceIndex index) := by
  let continuation :=
    sourceGeneratedPaidSuccessorBearerRoleIndependentContinuationAt oldVisit
      sourceIndex index
  let disposition :=
    canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index
  have priorAudit :
      PaidSuccessorBearerRoleIndependentContinuationAuditAt continuation := by
    exact paidSuccessorBearerRoleIndependentContinuationAuditAt oldVisit
      sourceIndex index
  have alignment := disposition.sameSuccessorPaymentActionAndLiability
  exact
    { canonicalExact := rfl
      priorContinuationAudit := priorAudit
      sameSuccessorPaymentActionAndLiability :=
        ⟨alignment.1, alignment.2.1, alignment.2.2.1,
          alignment.2.2.2.1, alignment.2.2.2.2.1⟩
      successorCompilerWriteAndActualExitExact :=
        ⟨PostContinuationExternalResidualDispositionAt.successorCompilerWriteExact
            (continuation := continuation),
          PostContinuationExternalResidualDispositionAt.successorActualExitFromWriteExact
            (continuation := continuation)⟩
      liabilityCrossRootOccurrenceDistinct :=
        disposition.liabilityCrossRootOccurrenceDistinct
      liabilitySourceProvenance := disposition.liability.paymentTrace
      externalResponsibility :=
        ⟨disposition.sourceOwnedResidual,
          disposition.rootConsumer,
          disposition.exactSettlement,
          disposition.actionableRenewal,
          disposition.rootFactorization⟩
      localDispositionAndExactNoErasure :=
        ⟨disposition.localLedgerEmpty,
          ⟨disposition.localDisposition⟩,
          disposition.localEmpty_doesNotEraseExactExternalLiability⟩
      substantiveLocalEmptyButExternalNonempty :=
        disposition.substantiveLocalDispositionEmpty_externalLiabilityNonempty
      installedExternalAuthorityNoErasure :=
        PostContinuationExternalResidualDispositionAt.installedExternalAuthorityNoErasure
          (continuation := continuation)
      servicesExternalSuccessorAndFurtherNext :=
        disposition.servicesExternalSuccessorAndFurtherNextRemain
      sourceOwnershipDeletionEmpty :=
        sourceOwnershipDeletion_isEmpty disposition
      rootConsumerDeletionEmpty := rootConsumerDeletion_isEmpty disposition
      localEmptyErasureEmpty :=
        localEmptyErasesExternalLiability_isEmpty disposition }

structure ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionCertificate :
    Prop where
  everyDisposition : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (CanonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
        oldVisit sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    PaidSuccessorPostContinuationExternalResidualDispositionAuditAt
      (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
        oldVisit sourceIndex index)
  everySourceOwnershipDeletionEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPostContinuationSourceOwnershipDeletionAt
          (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
            oldVisit sourceIndex index))
  everyRootConsumerDeletionEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPostContinuationRootConsumerDeletionAt
          (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
            oldVisit sourceIndex index))
  everyLocalEmptyErasureEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
          (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
            oldVisit sourceIndex index))

theorem proofCarryingPaidSuccessorPostContinuationExternalResidualDispositionDirectConsumer :
    ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionCertificate where
  everyDisposition := fun oldVisit sourceIndex index =>
    ⟨canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
      oldVisit sourceIndex index⟩
  everyAudit :=
    paidSuccessorPostContinuationExternalResidualDispositionAuditAt
  everySourceOwnershipDeletionEmpty := fun oldVisit sourceIndex index =>
    sourceOwnershipDeletion_isEmpty
      (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
        oldVisit sourceIndex index)
  everyRootConsumerDeletionEmpty := fun oldVisit sourceIndex index =>
    rootConsumerDeletion_isEmpty
      (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
        oldVisit sourceIndex index)
  everyLocalEmptyErasureEmpty := fun oldVisit sourceIndex index =>
    localEmptyErasesExternalLiability_isEmpty
      (canonicalPaidSuccessorPostContinuationExternalResidualDispositionAt
        oldVisit sourceIndex index)

end
end M14ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionRegression.paidSuccessorPostContinuationExternalResidualDispositionAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionRegression.proofCarryingPaidSuccessorPostContinuationExternalResidualDispositionDirectConsumer
