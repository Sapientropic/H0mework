import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.Risk.Merge.Capacity.NoFreeRestoration.ProofCarryingContributionCapacityNoFreeRestorationRegression

/-!
# Direct consumer of source-backed capacity reopening

The named runtime consumes the revised residual at depth `5`, while the
action's fixed source index generates periodic UBI payment, actual service and
an actionable-exit capacity of one.  The action-generated root still carries
only three zero-budget rows, proving that renewal did not counterfeit ledger
capacity.  Depth `6` consumes the target answer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityReopeningRuntimeRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open RootInquiryCompletion.NoFreeCapacityRestoration
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityNoFreeRestoration
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningActionSource
open M14SourceGeneratedSequentialContributionCapacityReopening
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningSupportSeparation
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity

abbrev ReopeningAction :=
  generatedContributionCapacityReopeningActionAt canonicalOldVisit 1

theorem fifthTick_contains_no_reopening_action :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
        fifthTick.resolution ReopeningAction) := by
  constructor
  rw [fifthTick_is_generated_selfU8_target_answer]
  exact fun impossible => impossible

theorem sixthTick_contains_no_u8_core
    {Core : Type 11} (core : Core) :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsU8Core
        sixthTick.resolution core) := by
  constructor
  rw [sixthTick_resolution_is_contributionCapacityReopening]
  exact fun impossible => impossible

def rawReopeningAction_cannot_wrap_runtime : PUnit := by
  fail_if_success
    exact (ReopeningAction :
      SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt
        jointRuntime.initialState)
  exact PUnit.unit

/-- A generated period-5 renewal is not a stored schedule and cannot be used
at the next root current, whose payload type requires period 6. -/
def one_period_witness_cannot_wrap_next_period : PUnit := by
  fail_if_success
    exact
      (ReopeningAction.receipt.periodicActualExitGenerated :
        Nonempty (PeriodicActualServiceExitAt 6))
  exact PUnit.unit

def contributionCapacityReopeningRenewalFace :
    SourceNativeRootSemanticFaceAt ReopeningAction.target.targetRoot
      ReopeningAction.target.targetVisit where
  projection := ContributionCapacityReopeningProjection.renewal
  active := PUnit.unit
  classifier_eq := rfl

theorem contributionCapacityReopeningRootGeneratedRenewal :
    Nonempty (PeriodicActualServiceExitAt 6) :=
  contributionCapacityReopeningRenewalFace.rootRead.down

theorem every_reopening_root_current_generates_actual_exit
    (index : Nat) :
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacityReopeningDepthAtCurrent 1 index)) :=
  contributionCapacityReopeningRootGeneratedRenewalAt canonicalOldVisit 1 index

theorem reopening_root_actual_exit_occurrences_injective :
    Function.Injective (fun index =>
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityReopeningDepthAtCurrent 1 index)) := by
  intro left right equality
  have depth_eq := periodicActualServiceExitOccurrenceAt_injective equality
  exact Nat.add_left_cancel depth_eq

theorem action_and_target_actual_exit_occurrences_distinct :
    periodicActualServiceExitOccurrenceAt 5 ≠
      periodicActualServiceExitOccurrenceAt 6 := by
  intro equality
  have depth_eq := periodicActualServiceExitOccurrenceAt_injective equality
  omega

structure ProofCarryingContributionCapacityReopeningRuntimeCertificate :
    Type 5 where
  reopeningResolution :
    sixthTick.resolution = .actualAction ReopeningAction
  reopeningKind : sixthTick.resolutionKind = .actualAction
  reopeningRuntimeResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      ReopeningAction jointRuntime 5
  sourceCurrent :
    (show Nat from
      (contributionCapacityReopeningActionSourceVisitAt canonicalOldVisit 1).current) = 3
  sourceEntry :
    contributionCapacityReopeningActionSourceEntryAt canonicalOldVisit 1 =
      contributionCapacityU8GeneratedResidual canonicalOldVisit
  sourceOccurrence :
    (contributionCapacityReopeningActionExactSourceEventAt canonicalOldVisit 1).occurrence =
      (CapacityU8RootAt canonicalOldVisit).emitted
        (contributionCapacityReopeningActionSourceVisitAt canonicalOldVisit 1).current
  periodicDepth : contributionCapacityReopeningDepthAt 1 = 5
  targetRenewalDepth : contributionCapacityReopeningDepthAtCurrent 1 1 = 6
  periodicPaymentGenerated : Nonempty (PeriodicSourceBackedPaymentAt 5)
  periodicActualExitGenerated : Nonempty (PeriodicActualServiceExitAt 5)
  rootRenewalProjectionGenerated : Nonempty (PeriodicActualServiceExitAt 6)
  everyRootCurrentGeneratesActualExit : ∀ index : Nat,
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacityReopeningDepthAtCurrent 1 index))
  rootActualExitOccurrencesInjective :
    Function.Injective (fun index =>
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityReopeningDepthAtCurrent 1 index))
  actionAndTargetActualExitOccurrencesDistinct :
    periodicActualServiceExitOccurrenceAt 5 ≠
      periodicActualServiceExitOccurrenceAt 6
  actionableRenewalGenerated : Nonempty
    (geometryCompilerAt 5).SourceGeneratedActionableExitRenewalAt
  actionableExitCapacityOne :
    (geometryCompilerAt 5).actionableExitCapacity = 1
  capturedExitCapacityZero :
    (capturedGeometryCompilerAt 5).actionableExitCapacity = 0
  initialNoFresh :
    (targetEntry :
      (contributionCapacityReopeningInitialLedger canonicalOldVisit).Entry) →
      Nonempty (Sigma fun oldEntry :
        (contributionCapacityU8Ledger canonicalOldVisit).Entry =>
        PLift (ReopeningAction.target.initialOpenLedger.forward oldEntry =
          targetEntry))
  targetLedgerExactlyThree :
    (entry :
      (contributionCapacityReopeningTargetLedger canonicalOldVisit).Entry) →
      entry = contributionCapacityReopeningEntryAt canonicalOldVisit true 0 ∨
      entry = contributionCapacityReopeningEntryAt canonicalOldVisit true 1 ∨
      entry = contributionCapacityReopeningEntryAt canonicalOldVisit true 2
  targetLedgerAllZero :
    (entry :
      (contributionCapacityReopeningTargetLedger canonicalOldVisit).Entry) →
      entry.progressBudget = 0
  targetLedgerHasNoPositiveProgress :
    IsEmpty (PositiveProgressEntryAt
      (contributionCapacityReopeningTargetLedger canonicalOldVisit))
  budgetAndExitCapacityRemainDistinct :
    ((entry :
      (contributionCapacityReopeningTargetLedger canonicalOldVisit).Entry) →
        entry.progressBudget = 0) ∧
      (geometryCompilerAt 5).actionableExitCapacity = 1
  exhaustedRootCannotSelfRefill :
    NoEndogenousPositiveRestorationAt canonicalOldVisit
  generatedResidualUsesExistingBearer :
    contributionCapacityU8BearerAt canonicalOldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityU8GeneratedResidual canonicalOldVisit) =
      sourceGeneratedLossAllocationMaterial.parentBearer
  targetLawIsRootSemantic :
    ReopeningAction.target.targetTheory =
      TheoryState.rootSemantic (ReopeningNAt canonicalOldVisit)
  targetSupportCard : Nat.card (ReopeningNAt canonicalOldVisit).Support = 50
  reopenedTargetAnswered :
    seventhTick.resolution =
      .directlyAnswered
        (contributionCapacityReopenedAnswerFaceAt canonicalOldVisit 1 0)
        (contributionCapacityReopenedAnswerConsumerAt canonicalOldVisit 1 0)
  previousTickNoReopeningAction :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
        fifthTick.resolution ReopeningAction)
  reopeningTickNoU8 :
    ∀ {Core : Type 11} (core : Core),
      IsEmpty
        (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsU8Core
          sixthTick.resolution core)

def proofCarryingContributionCapacityReopeningRuntimeCertificate :
    ProofCarryingContributionCapacityReopeningRuntimeCertificate where
  reopeningResolution :=
    sixthTick_resolution_is_contributionCapacityReopening
  reopeningKind := sixthTick_resolutionKind_is_actualAction
  reopeningRuntimeResumption := contributionCapacityReopeningResumption
  sourceCurrent := rfl
  sourceEntry := rfl
  sourceOccurrence := rfl
  periodicDepth := rfl
  targetRenewalDepth := rfl
  periodicPaymentGenerated := ReopeningAction.receipt.periodicPaymentGenerated
  periodicActualExitGenerated :=
    ReopeningAction.receipt.periodicActualExitGenerated
  rootRenewalProjectionGenerated :=
    contributionCapacityReopeningRootGeneratedRenewal
  everyRootCurrentGeneratesActualExit :=
    every_reopening_root_current_generates_actual_exit
  rootActualExitOccurrencesInjective :=
    reopening_root_actual_exit_occurrences_injective
  actionAndTargetActualExitOccurrencesDistinct :=
    action_and_target_actual_exit_occurrences_distinct
  actionableRenewalGenerated :=
    ReopeningAction.receipt.actionableRenewalGenerated
  actionableExitCapacityOne :=
    ReopeningAction.receipt.actionableExitCapacityOne
  capturedExitCapacityZero :=
    ReopeningAction.receipt.capturedExitCapacityZero
  initialNoFresh := ReopeningAction.target.initialLedgerNoFresh
  targetLedgerExactlyThree :=
    contributionCapacityReopeningEntry_cases canonicalOldVisit true
  targetLedgerAllZero := ReopeningAction.receipt.targetLedgerAllZero
  targetLedgerHasNoPositiveProgress :=
    ReopeningAction.receipt.targetLedgerHasNoPositiveProgress
  budgetAndExitCapacityRemainDistinct :=
    ⟨ReopeningAction.receipt.targetLedgerAllZero,
      ReopeningAction.receipt.actionableExitCapacityOne⟩
  exhaustedRootCannotSelfRefill :=
    ReopeningAction.receipt.exhaustedRootCannotSelfRefill
  generatedResidualUsesExistingBearer :=
    ReopeningAction.receipt.generatedResidualUsesExistingBearer
  targetLawIsRootSemantic := rfl
  targetSupportCard := reopeningSupport_card
  reopenedTargetAnswered := seventhTick_is_generated_reopening_target_answer
  previousTickNoReopeningAction := fifthTick_contains_no_reopening_action
  reopeningTickNoU8 := sixthTick_contains_no_u8_core

end
end M14ProofCarryingContributionCapacityReopeningRuntimeRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningRuntimeRegression.proofCarryingContributionCapacityReopeningRuntimeCertificate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningRuntimeRegression.rawReopeningAction_cannot_wrap_runtime
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningRuntimeRegression.one_period_witness_cannot_wrap_next_period
