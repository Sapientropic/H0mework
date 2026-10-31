import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Execution.Producer.SourceGeneratedContributionCapacityCofinalNoveltyU8Compilation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Runtime.SourceGeneratedPostSettlementObserverSubmissionU8Runtime
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedAuthority

/-!
# Sole actual runtime for one cofinally later augmented U8 occurrence

The existing cofinal novelty execution and the observer-submission renewal now
consume one definitionally shared rich U8 core.  This public runtime is the
cofinal API for the submission runtime: it does not construct a sibling root,
compiler, core, schedule or completed future.  Its source state is the exact
right-replay Payment occurrence; its first macro successor is the augmented
revision's generated target, and later ticks follow that same revised root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal Legislation
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Compilation

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary}
  {rootedBridge :
    SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty}
  {revisionBridge :
    SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt rootedBridge}
  (execution :
    SourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
      revisionBridge)

/-- The old cofinal runtime API is the submission-augmented process itself. -/
def process : SourceNativeInquiryEngineProcess.{0} := by
  cases execution
  exact
    M14SourceGeneratedPostSettlementObserverSubmissionU8.processAt
      oldVisit sourceIndex boundary

/-- No second runtime: this is definitionally the augmented runtime. -/
def runtime : SourceNativeInquiryRuntime (process execution) := by
  cases execution
  exact
    M14SourceGeneratedPostSettlementObserverSubmissionU8.runtimeAt
      oldVisit sourceIndex boundary

def firstTick := (runtime execution).tickAt 0

@[simp] theorem executionCore_isAugmentedCore :
    execution.core =
      M14SourceGeneratedPostSettlementObserverSubmissionU8.generatedU8CoreAt
        oldVisit sourceIndex boundary := by
  rw [SourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt.compilationCore_isVisitIndexedRevision
    execution]
  cases revisionBridge
  rfl

theorem process_isSubmissionProcess : HEq
    (process execution)
    (M14SourceGeneratedPostSettlementObserverSubmissionU8.processAt
      oldVisit sourceIndex boundary) := by
  cases execution
  exact HEq.rfl

theorem runtime_isSubmissionRuntime : HEq
    (runtime execution)
    (M14SourceGeneratedPostSettlementObserverSubmissionU8.runtimeAt
      oldVisit sourceIndex boundary) := by
  cases execution
  exact HEq.rfl

@[simp] theorem firstTick_resolution_isExactCore :
    (firstTick execution).resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure execution.core := by
  rw [executionCore_isAugmentedCore execution]
  cases execution
  exact
    M14SourceGeneratedPostSettlementObserverSubmissionU8.firstTick_resolution_isExactCore
      oldVisit sourceIndex boundary

theorem runtimeConsumesExactCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt execution.core
      (runtime execution) 0 := by
  rw [executionCore_isAugmentedCore execution]
  cases execution
  exact M14SourceGeneratedPostSettlementObserverSubmissionU8.runtimeConsumesExactCore
    oldVisit sourceIndex boundary

def sourceInstalled :
    SourceInstalledRenewalAt
      M9ProofCarryingRenewalInquiryRoot.jointRecognition
      (M14UBIPeriodicRootHistory.temporalVisitAt
        rootedBridge.rightCurrent) := by
  cases execution
  exact SourceInstalledRenewalAt.generate PUnit.unit rfl

theorem runtimeSplice : SourceInstalledRenewalRuntimeSpliceAt
    (root := jointRoot)
    (recognition := M9ProofCarryingRenewalInquiryRoot.jointRecognition)
    (visit := M14UBIPeriodicRootHistory.temporalVisitAt
      rootedBridge.rightCurrent)
    (process := process execution)
    (sourceInstalled execution) (runtime execution) 0 where
  sameRoot := HEq.rfl
  sameVisit := HEq.rfl
  sameRow := HEq.rfl
  sameOccurrence := HEq.rfl

theorem rightPaymentInstallation_exact :
    rootedBridge.rightReplay.2.futureBirth.actualExit.paymentOccurrence.installed =
      M14UBIPeriodicRootHistory.installedUBIAt rootedBridge.rightCurrent :=
  rootedBridge.rightPaymentInstalled_exact

theorem sourceInstalledOccurrence_isRightPaymentOccurrence :
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (M14UBIPeriodicRootHistory.temporalVisitAt
          rootedBridge.rightCurrent) =
      (rootedBridge.rightReplay.2.futureBirth.actualExit.paymentOccurrence
        ).rootOccurrence :=
  rootedBridge.rightPaymentRootOccurrence_exact.symm

end
end M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.executionCore_isAugmentedCore
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtime_isSubmissionRuntime
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtimeConsumesExactCore
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtimeSplice
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.sourceInstalledOccurrence_isRightPaymentOccurrence
