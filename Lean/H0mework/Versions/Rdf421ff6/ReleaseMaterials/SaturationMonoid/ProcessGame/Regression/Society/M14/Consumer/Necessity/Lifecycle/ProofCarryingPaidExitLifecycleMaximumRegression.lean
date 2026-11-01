import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.NoGo.SourceGeneratedPaidExitLifecycleMaximumNoGo
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Disposition.ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionRegression

/-!
# Direct consumer of the paid-exit lifecycle maximum

The audit consumes the independent maximum characterization, the three exact
Payment edges, four-stage action/authority/K separation, execution,
role-independent continuation, external residual disposition, services and
future.  It also consumes the full-capture counterlife, observer no-section
and all responsibility-deletion controls.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPaidExitLifecycleMaximumRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPaidExitLifecycleMaximumCharacterization
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPaidExitLifecycleMaximumNoGo
open M14ProofCarryingPaidSuccessorPostContinuationExternalResidualDispositionRegression

abbrev CanonicalPaidExitLifecycleMaximumAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex index

def canonicalPaidExitLifecycleMaximumAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index :=
  sourceGeneratedProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
    index

structure PaidExitLifecycleMaximumAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (lifecycle : CanonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) : Prop where
  priorDispositionAudit :
    PaidSuccessorPostContinuationExternalResidualDispositionAuditAt
      lifecycle.disposition
  independentMaximumCharacterizations :
    (Nonempty
          (CanonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index) ↔
        PaidExitLifecycleMaximumContractAt oldVisit sourceIndex index) ∧
      (Nonempty
          (birthBearerGeometryCompilerAt
            (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
          ).SourceGeneratedActionableExitRenewalAt ↔
        PaidExitLifecycleActionableRenewalContractAt oldVisit sourceIndex index) ∧
      (Nonempty
          (birthBearerCapturedGeometryCompilerAt
            (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
          ).SourceGeneratedActionableExitRenewalAt ↔
        PaidExitLifecycleFullCaptureContractAt oldVisit sourceIndex index)
  exactThreePaidSuccessorEdges :
    HEq
        (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
          ).sourcePayment.nextPaidBy
        (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
          ).targetConsequence.outerRootEvent.occurrence ∧
      HEq lifecycle.continuation.executedPayment.nextPaidBy
        lifecycle.continuation.successorRootEvent.occurrence ∧
      HEq lifecycle.continuation.successorPayment.nextPaidBy
        (paidExitLifecycleFurtherPaidStepAt oldVisit sourceIndex index
          ).targetRootEvent.occurrence
  exactPaymentChain :
    (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
        ).targetPayment = lifecycle.continuation.executedPayment ∧
      lifecycle.continuation.successorStandingRenewal.sourcePayment =
        lifecycle.continuation.executedPayment ∧
      lifecycle.continuation.successorStandingRenewal.targetPayment =
        lifecycle.continuation.successorPayment ∧
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
          ).sourcePayment = lifecycle.continuation.successorPayment ∧
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
          ).targetPayment =
        (paidExitLifecycleFurtherPaidStepAt oldVisit sourceIndex index
          ).targetPayment ∧
      (paidExitLifecycleFurtherStandingRenewalAt oldVisit sourceIndex index
          ).targetConsequence.outerRootEvent =
        (paidExitLifecycleFurtherPaidStepAt oldVisit sourceIndex index
          ).targetRootEvent
  everyDistinctStageSameActionDifferentAuthorityAndK :
    ∀ left right : PaidExitLifecycleStage, left ≠ right →
      paidExitLifecycleActionReadoutAt oldVisit sourceIndex index left =
          paidExitLifecycleActionReadoutAt oldVisit sourceIndex index right ∧
        paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index left ≠
          paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index right ∧
        paidExitLifecycleActualServiceKAt oldVisit sourceIndex index left ≠
          paidExitLifecycleActualServiceKAt oldVisit sourceIndex index right
  responseExecution :
    PaidExitLifecycleResponseExecutionAt oldVisit sourceIndex index
  roleIndependentContinuation :
    PaidExitLifecycleRoleIndependentContinuationAt oldVisit sourceIndex index
      lifecycle.actionableRenewal.code
  externalDisposition :
    PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex index
  servicesAndFuture :
    PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex index
  fullCaptureCounterlife : Nonempty
    (ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex index)
  fullCapturePreservesBareFutureAndNoncaptureAxes :
    ∃ counterlife :
        ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex index,
      Nonempty
          (birthBearerExitRelationCompiler.FutureContinuationAt
            birthBearerIndependentExitRelation.1 .target
              counterlife.positive.continuation.successorContinuationAction.1) ∧
        counterlife.continuationCountermodel.relationLevelActionable =
          birthBearerLeave_target_actionable ∧
        birthBearerFullCapture.Captures
          counterlife.positive.continuation.successorContinuationAction.1 ∧
        birthBearerCapturedProgram.purchasingPowerStanding =
          birthBearerExitCapacityProgram.purchasingPowerStanding ∧
        birthBearerCapturedProgram.employmentLoss =
          birthBearerExitCapacityProgram.employmentLoss ∧
        birthBearerCapturedProgram.exitInterest =
          birthBearerExitCapacityProgram.exitInterest ∧
        Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
        Nonempty
          (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
            counterlife.positive.continuation.paidContinuationStep.targetCurrent.actualExit)
  fullCaptureReportedMaximumEmpty :
    ∀ counterlife :
      ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex index,
      IsEmpty
        (ExactFullCaptureReportedPaidExitLifecycleMaximumAt counterlife)
  actionReadoutLeftInverseEmpty : IsEmpty
    (ExactPaidExitLifecycleActionReadoutLeftInverseAt lifecycle)
  sourceOwnershipDeletionEmpty : IsEmpty
    (ExactPostContinuationSourceOwnershipDeletionAt lifecycle.disposition)
  rootConsumerDeletionEmpty : IsEmpty
    (ExactPostContinuationRootConsumerDeletionAt lifecycle.disposition)
  localEmptyErasureEmpty : IsEmpty
    (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
      lifecycle.disposition)

theorem paidExitLifecycleMaximumAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidExitLifecycleMaximumAuditAt
      (canonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index) := by
  let lifecycle :=
    canonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index
  let counterlife :=
    proofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex index
  have priorAudit :
      PaidSuccessorPostContinuationExternalResidualDispositionAuditAt
        lifecycle.disposition := by
    exact paidSuccessorPostContinuationExternalResidualDispositionAuditAt
      oldVisit sourceIndex index
  exact
    { priorDispositionAudit := priorAudit
      independentMaximumCharacterizations :=
        ⟨ProofCarryingPaidExitLifecycleMaximumAt.nonempty_iff_maximumContract
            oldVisit sourceIndex index,
          installedActionableRenewal_iff_fullContract oldVisit sourceIndex
            index,
          fullCaptureActionableRenewal_iff_fullContract oldVisit sourceIndex
            index⟩
      exactThreePaidSuccessorEdges :=
        lifecycle.exactThreePaidSuccessorEdges
      exactPaymentChain := lifecycle.rooted.occurrenceSpine.paymentChainExact
      everyDistinctStageSameActionDifferentAuthorityAndK :=
        lifecycle.everyDistinctStage_sameAction_differentAuthorityAndK
      responseExecution := lifecycle.rooted.responseExecution
      roleIndependentContinuation :=
        lifecycle.rooted.roleIndependentContinuation
      externalDisposition := lifecycle.rooted.externalDisposition
      servicesAndFuture := lifecycle.rooted.servicesAndFuture
      fullCaptureCounterlife := ⟨counterlife⟩
      fullCapturePreservesBareFutureAndNoncaptureAxes :=
        ⟨counterlife,
          counterlife.bareFuturePaymentEmploymentInterestAndResponsibilityRemain⟩
      fullCaptureReportedMaximumEmpty :=
        fullCaptureReportedPaidExitLifecycleMaximum_isEmpty
      actionReadoutLeftInverseEmpty :=
        paidExitLifecycleActionReadoutLeftInverse_isEmpty lifecycle
      sourceOwnershipDeletionEmpty :=
        lifecycleSourceOwnershipDeletion_isEmpty lifecycle
      rootConsumerDeletionEmpty :=
        lifecycleRootConsumerDeletion_isEmpty lifecycle
      localEmptyErasureEmpty :=
        lifecycleLocalEmptyErasure_isEmpty lifecycle }

structure ProofCarryingPaidExitLifecycleMaximumCertificate : Prop where
  everyLifecycle : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty (CanonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    PaidExitLifecycleMaximumAuditAt
      (canonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index)
  everyFullCaptureCounterlife :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      Nonempty
        (ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex
          index)
  everyFullCaptureReportedMaximumEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactFullCaptureReportedPaidExitLifecycleMaximumAt
          (proofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex
            index))
  everyActionReadoutLeftInverseEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactPaidExitLifecycleActionReadoutLeftInverseAt
          (canonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index))

theorem proofCarryingPaidExitLifecycleMaximumDirectConsumer :
    ProofCarryingPaidExitLifecycleMaximumCertificate where
  everyLifecycle := fun oldVisit sourceIndex index =>
    ⟨canonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index⟩
  everyAudit := paidExitLifecycleMaximumAuditAt
  everyFullCaptureCounterlife := fun oldVisit sourceIndex index =>
    ⟨proofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex index⟩
  everyFullCaptureReportedMaximumEmpty := fun oldVisit sourceIndex index =>
    fullCaptureReportedPaidExitLifecycleMaximum_isEmpty
      (proofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex index)
  everyActionReadoutLeftInverseEmpty := fun oldVisit sourceIndex index =>
    paidExitLifecycleActionReadoutLeftInverse_isEmpty
      (canonicalPaidExitLifecycleMaximumAt oldVisit sourceIndex index)

end
end M14ProofCarryingPaidExitLifecycleMaximumRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidExitLifecycleMaximumRegression.paidExitLifecycleMaximumAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidExitLifecycleMaximumRegression.proofCarryingPaidExitLifecycleMaximumDirectConsumer
