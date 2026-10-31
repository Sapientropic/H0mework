import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.Producer.SourceGeneratedProofCarryingPaidExitLifecycleMaximum

/-!
# Exact no-go controls for the paid-exit lifecycle maximum

Full capture preserves the actual Payment chain, bare future, relation-level
actionability, employment/payment/interest axes, external responsibility and
generated next.  It deletes only the capture-adjusted actionable-renewal
mouth.  The constant action readout also admits no left inverse to the four
distinct authority stages.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidExitLifecycleMaximumNoGo

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
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPaidExitLifecycleMaximumCharacterization
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum

structure ProofCarryingFullCapturePaidExitCounterlifeAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 32 where
  private mk ::
  positive : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex index
  continuationCountermodel :
    ExactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
      positive.continuation
  retaliationCountermodel :
    ExactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit sourceIndex
      index
  nominalTransfer : NominalTransferReadoutAt birthBearerCapturedProgram
  capturedRenewalEmpty : IsEmpty
    (birthBearerCapturedGeometryCompilerAt
      (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
    ).SourceGeneratedActionableExitRenewalAt
  occurrenceSpinePreserved :
    PaidExitLifecycleOccurrenceSpineAt oldVisit sourceIndex index
  externalDispositionPreserved :
    PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex index
  servicesAndFuturePreserved :
    PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex index

def proofCarryingFullCapturePaidExitCounterlifeAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex index := by
  let positive :=
    sourceGeneratedProofCarryingPaidExitLifecycleMaximumAt oldVisit
      sourceIndex index
  exact
    { positive := positive
      continuationCountermodel :=
        exactPaidSuccessorFullCaptureRoleIndependentContinuationCountermodelAt
          oldVisit sourceIndex index
      retaliationCountermodel :=
        exactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
          sourceIndex index
      nominalTransfer := birthBearerNominalTransfer
      capturedRenewalEmpty :=
        paidExitLifecycleFullCaptureRenewal_isEmpty oldVisit sourceIndex index
      occurrenceSpinePreserved := positive.rooted.occurrenceSpine
      externalDispositionPreserved := positive.rooted.externalDisposition
      servicesAndFuturePreserved := positive.rooted.servicesAndFuture }

namespace ProofCarryingFullCapturePaidExitCounterlifeAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (counterlife : ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit
    sourceIndex index)

include counterlife

/-- Full capture leaves every noncapture-independent axis used by the
lifecycle consumer. -/
theorem bareFuturePaymentEmploymentInterestAndResponsibilityRemain :
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
          counterlife.positive.continuation.paidContinuationStep.targetCurrent.actualExit) :=
  ⟨⟨counterlife.continuationCountermodel.bareFuture⟩,
    rfl,
    counterlife.continuationCountermodel.sameActionCaptured,
    counterlife.continuationCountermodel.installedPaymentAxisExact,
    counterlife.continuationCountermodel.installedEmploymentAxisExact,
    counterlife.continuationCountermodel.installedExitInterestAxisExact,
    counterlife.externalDispositionPreserved.sourceOwnedResidual,
    counterlife.externalDispositionPreserved.rootConsumer⟩

end ProofCarryingFullCapturePaidExitCounterlifeAt

structure ExactFullCaptureReportedPaidExitLifecycleMaximumAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (counterlife : ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit
      sourceIndex index) : Type 32 where
  falseRenewal :
    (birthBearerCapturedGeometryCompilerAt
      (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
    ).SourceGeneratedActionableExitRenewalAt

theorem fullCaptureReportedPaidExitLifecycleMaximum_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (counterlife : ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit
      sourceIndex index) :
    IsEmpty
      (ExactFullCaptureReportedPaidExitLifecycleMaximumAt counterlife) :=
  ⟨fun falseReport =>
    counterlife.capturedRenewalEmpty.false falseReport.falseRenewal⟩

structure ExactPaidExitLifecycleActionReadoutLeftInverseAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (_positive : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) : Type 32 where
  decode : birthBearerExitExerciseController.ExactActionSeed →
    PaidExitLifecycleStage
  leftInverse : Function.LeftInverse decode
    (paidExitLifecycleActionReadoutAt oldVisit sourceIndex index)

theorem paidExitLifecycleActionReadoutLeftInverse_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (positive : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) :
    IsEmpty (ExactPaidExitLifecycleActionReadoutLeftInverseAt positive) := by
  let stage0 : PaidExitLifecycleStage := ⟨0, by decide⟩
  let stage1 : PaidExitLifecycleStage := ⟨1, by decide⟩
  have stagesDistinct : stage0 ≠ stage1 := by decide
  exact
    ⟨fun reconstruction =>
      stagesDistinct
        (reconstruction.leftInverse.injective
          (positive.everyDistinctStage_sameAction_differentAuthorityAndK
            stage0 stage1 stagesDistinct).1)⟩

theorem lifecycleSourceOwnershipDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (positive : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) :
    IsEmpty
      (ExactPostContinuationSourceOwnershipDeletionAt positive.disposition) :=
  sourceOwnershipDeletion_isEmpty positive.disposition

theorem lifecycleRootConsumerDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (positive : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) :
    IsEmpty
      (ExactPostContinuationRootConsumerDeletionAt positive.disposition) :=
  rootConsumerDeletion_isEmpty positive.disposition

theorem lifecycleLocalEmptyErasure_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (positive : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) :
    IsEmpty
      (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
        positive.disposition) :=
  localEmptyErasesExternalLiability_isEmpty positive.disposition

end
end M14SourceGeneratedPaidExitLifecycleMaximumNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidExitLifecycleMaximumNoGo.proofCarryingFullCapturePaidExitCounterlifeAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidExitLifecycleMaximumNoGo.fullCaptureReportedPaidExitLifecycleMaximum_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidExitLifecycleMaximumNoGo.paidExitLifecycleActionReadoutLeftInverse_isEmpty
