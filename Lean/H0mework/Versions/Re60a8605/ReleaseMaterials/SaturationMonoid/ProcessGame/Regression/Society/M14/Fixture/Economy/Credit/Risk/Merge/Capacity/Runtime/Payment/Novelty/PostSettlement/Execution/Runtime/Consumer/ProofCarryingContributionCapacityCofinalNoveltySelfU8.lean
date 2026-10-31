import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Execution.Runtime.Producer.SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Revision.SourceGeneratedReflexiveSelfU8

/-!
# Proof-carrying cofinal novelty self-U8

One pointwise novelty token now determines the right paid replay, its exact
external M9 occurrence, the installed U8 compilation, a named runtime that
consumes that core, the same-visit proof-carrying legislation coordinate and
the reflexive self-U8 seal.  The current post-root `rootSemantic` remains
failure-free; revision authority comes only from the existing narrow M9 root
carried by the rich Payment.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityCofinalNoveltySelfU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery
open Renewal Legislation Theory.Revision
open Society.Revision
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14ProofCarryingContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Compilation
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  {novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary}
  {rootedBridge :
    SourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty}
  {revisionBridge :
    SourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt rootedBridge}
  (execution :
    SourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
      revisionBridge)

def legislation : ProofCarryingLegislationAt
    (sourceInstalled execution) (runtime execution) 0
      (runtimeSplice execution) :=
  sourceGeneratedProofCarryingLegislation (sourceInstalled execution)
    (runtime execution) 0 (runtimeSplice execution)

def exactRevolutionaryConsumption :=
  (legislation execution).revolutionaryConsumption?.get (by rfl)

def exactRevolution := (exactRevolutionaryConsumption execution).1

def exactConsumption := (exactRevolutionaryConsumption execution).2

def selfU8 : SourceGeneratedReflexiveSelfU8At
    (legislation execution) (exactRevolution execution)
      (exactConsumption execution) :=
  SourceGeneratedReflexiveSelfU8At.generate (exactConsumption execution)

@[simp] theorem exactRevolution_core_isExecutionCore :
    (exactRevolution execution).core = execution.core :=
  rfl

@[simp] theorem selfU8_failure_isExistingM9Failure :
    (selfU8 execution).failure =
      RootInquiryU8CompletionRegression.failure :=
  rfl

@[simp] theorem selfU8_rooted_isPaidVisitRooted :
    (selfU8 execution).rooted = rootedBridge.rightRootedFailure :=
  revisionBridge.rightCore_rooted_exact

@[simp] theorem selfU8_coface_isPaidVisitCoface :
    (selfU8 execution).minimalCoface = rootedBridge.rightMinimalCoface :=
  revisionBridge.rightCore_coface_exact

theorem selfU8_runtimeConsumesExactCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt execution.core
      (runtime execution) 0 :=
  (selfU8 execution).runtime_consumes_core

@[simp] theorem selfU8_firstWrite_isCompilerGenerated :
    (selfU8 execution).firstWrite = revisionBridge.rightFirstWrite :=
  rfl

theorem selfU8_firstWriteConsumes_exact :
    HEq (selfU8 execution).firstWriteConsumes
      revisionBridge.rightFirstWriteConsumes :=
  HEq.rfl

theorem selfU8_revisedRows_shareGeneratedNext :
    (selfU8 execution).oldRowAnswerAndNext.nextCurrent =
      (selfU8 execution).newRowAnswerAndNext.nextCurrent :=
  (selfU8 execution).revised_rows_share_generatedNext

theorem selfU8_sameRoot : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt (runtime execution) 0
      ).1.state.base.root jointRoot :=
  (selfU8 execution).sameRoot

theorem selfU8_sameVisit : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt (runtime execution) 0
      ).1.state.base.visit
    (M14UBIPeriodicRootHistory.temporalVisitAt rootedBridge.rightCurrent) :=
  (selfU8 execution).sameVisit

theorem selfU8_sameOccurrenceAsRightPayment : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt (runtime execution) 0
      ).1.state.base.root.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt
          (sourceGeneratedRuntimeInquiryCoordinateAt (runtime execution) 0
            ).1.state.base.visit)
    (rootedBridge.rightReplay.2.futureBirth.actualExit.paymentOccurrence
      ).rootOccurrence := by
  exact HEq.trans (selfU8 execution).sameOccurrence
    (heq_of_eq
      sourceInstalledOccurrence_isRightPaymentOccurrence)

theorem selfU8_rootFactorization :
    (sourceInstalled execution).RootAnswerAndNextFactorizes :=
  (selfU8 execution).rootAnswerAndNext_factorizes

theorem rightRecoveryOldRow_nonempty :
    Nonempty
      (SourceNativeLivingCausalEntryAnswerAndNextAt
        revisionBridge.rightCore.revision.generate.newLivingRoot
        (oldFirstWriteSuccessor revisionBridge.rightCore.revision).targetVisit
        (oldFirstWriteSuccessor revisionBridge.rightCore.revision).targetEntry
        (oldFirstWriteTargetAuthority revisionBridge.rightCore.revision)) :=
  ⟨revisionBridge.rightRecovery.2.1⟩

theorem rightRecoveryNewRow_nonempty :
    Nonempty
      (SourceNativeLivingCausalEntryAnswerAndNextAt
        revisionBridge.rightCore.revision.generate.newLivingRoot
        (newFirstWriteSuccessor revisionBridge.rightCore.revision).targetVisit
        (newFirstWriteSuccessor revisionBridge.rightCore.revision).targetEntry
        (newFirstWriteTargetAuthority revisionBridge.rightCore.revision)) :=
  ⟨revisionBridge.rightRecovery.2.2⟩

structure ProofCarryingContributionCapacityCofinalNoveltySelfU8CertificateAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Prop where
  noveltyConsumed : Nonempty
    (ConsumedContributionCapacityCofinalProductiveNoveltyAt oldVisit
      sourceIndex boundary)
  bothPathsLater :
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    boundary < consumed.2.leftReplay.2.current ∧
      boundary < consumed.2.rightReplay.2.current
  actualPathsDifferent :
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    consumed.2.leftReplay.2.actualPath ≠
      consumed.2.rightReplay.2.actualPath
  sameNormalDifferentK :
    let consumed :=
      proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let observer :=
      contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex
    observer.forget consumed.2.leftReplay =
        observer.forget consumed.2.rightReplay ∧
      observer.authorityK consumed.2.leftReplay ≠
        observer.authorityK consumed.2.rightReplay
  rightPaymentRooted :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let rootedBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    rootedBridge.rightRootedFailure.oldBoundaryEvolution.occurrence =
      (rootedBridge.rightReplay.2.futureBirth.actualExit.paymentOccurrence
        ).rootOccurrence.occurrence
  runtimeConsumesCore :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let rootedBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    let revisionBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
        rootedBridge
    let execution :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
        revisionBridge
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt execution.core
      (runtime execution) 0
  runtimeSpliceExact :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let rootedBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    let revisionBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
        rootedBridge
    let execution :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
        revisionBridge
    SourceInstalledRenewalRuntimeSpliceAt
      (sourceInstalled execution) (runtime execution) 0
  selfU8OccurrenceIsRightPayment :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let rootedBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    let revisionBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
        rootedBridge
    let execution :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
        revisionBridge
    HEq
      ((sourceGeneratedRuntimeInquiryCoordinateAt (runtime execution) 0
        ).1.state.base.root.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt
            (sourceGeneratedRuntimeInquiryCoordinateAt (runtime execution) 0
              ).1.state.base.visit)
      (rootedBridge.rightReplay.2.futureBirth.actualExit.paymentOccurrence
        ).rootOccurrence
  exactSelfU8 :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let rootedBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    let revisionBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
        rootedBridge
    let execution :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
        revisionBridge
    Nonempty
      (SourceGeneratedReflexiveSelfU8At
        (legislation execution) (exactRevolution execution)
          (exactConsumption execution))
  sameRootExistingFailure :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let rootedBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    let revisionBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
        rootedBridge
    let execution :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
        revisionBridge
    (selfU8 execution).failure = RootInquiryU8CompletionRegression.failure ∧
      (selfU8 execution).rooted = rootedBridge.rightRootedFailure ∧
      (selfU8 execution).minimalCoface = rootedBridge.rightMinimalCoface
  firstWriteAndRecovery :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let rootedBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    let revisionBridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
        rootedBridge
    let execution :=
      sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
        revisionBridge
    (selfU8 execution).firstWrite = revisionBridge.rightFirstWrite ∧
      Nonempty
        (SourceNativeLivingCausalEntryAnswerAndNextAt
          revisionBridge.rightCore.revision.generate.newLivingRoot
          (oldFirstWriteSuccessor
            revisionBridge.rightCore.revision).targetVisit
          (oldFirstWriteSuccessor
            revisionBridge.rightCore.revision).targetEntry
          (oldFirstWriteTargetAuthority revisionBridge.rightCore.revision)) ∧
      Nonempty
        (SourceNativeLivingCausalEntryAnswerAndNextAt
          revisionBridge.rightCore.revision.generate.newLivingRoot
          (newFirstWriteSuccessor
            revisionBridge.rightCore.revision).targetVisit
          (newFirstWriteSuccessor
            revisionBridge.rightCore.revision).targetEntry
          (newFirstWriteTargetAuthority revisionBridge.rightCore.revision))
  postRootCannotFakeFailure :
    ∀ {support : (JointSettlementNAt oldVisit).Support},
      ∀ obstruction : (JointSettlementNAt oldVisit).ObstructionAt support,
        IsEmpty
          (ActualExpressibilityFailure
            (ContributionCapacityPostSettlementRenewalRootAt oldVisit
              sourceIndex).source.base.lawSurface obstruction)

theorem proofCarryingContributionCapacityCofinalNoveltySelfU8At
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ProofCarryingContributionCapacityCofinalNoveltySelfU8CertificateAt oldVisit
      sourceIndex boundary := by
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  let rootedBridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
  let revisionBridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt rootedBridge
  let execution :=
    sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
      revisionBridge
  exact
    { noveltyConsumed :=
        ⟨proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
          sourceIndex boundary⟩
      bothPathsLater :=
        (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
          sourceIndex boundary).2.bothStrictlyLater
      actualPathsDifferent :=
        (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
          sourceIndex boundary).2.actualPathsDifferent
      sameNormalDifferentK :=
        (proofCarryingContributionCapacityCofinalProductiveNoveltyAt oldVisit
          sourceIndex boundary).2.sameRealNormalForm_differentActualK
      rightPaymentRooted :=
        rootedBridge.rightRootedOccurrence_isPaymentOccurrence
      runtimeConsumesCore := runtimeConsumesExactCore execution
      runtimeSpliceExact := runtimeSplice execution
      selfU8OccurrenceIsRightPayment :=
        selfU8_sameOccurrenceAsRightPayment execution
      exactSelfU8 := ⟨selfU8 execution⟩
      sameRootExistingFailure :=
        ⟨selfU8_failure_isExistingM9Failure execution,
          selfU8_rooted_isPaidVisitRooted execution,
          selfU8_coface_isPaidVisitCoface execution⟩
      firstWriteAndRecovery :=
        ⟨selfU8_firstWrite_isCompilerGenerated execution,
          rightRecoveryOldRow_nonempty,
          rightRecoveryNewRow_nonempty⟩
      postRootCannotFakeFailure := fun obstruction =>
        contributionCapacityPostSettlementRootSemantic_failureIsEmpty oldVisit
          sourceIndex obstruction }

structure ProofCarryingContributionCapacityCofinalNoveltySelfU8Certificate
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  everyBoundary : ∀ boundary : Nat,
    ProofCarryingContributionCapacityCofinalNoveltySelfU8CertificateAt oldVisit
      sourceIndex boundary

theorem proofCarryingContributionCapacityCofinalNoveltySelfU8
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityCofinalNoveltySelfU8Certificate oldVisit
      sourceIndex where
  everyBoundary :=
    proofCarryingContributionCapacityCofinalNoveltySelfU8At oldVisit sourceIndex

set_option linter.unusedVariables false in
theorem bareNoveltyFragmentsCannotRetypeAsSelfU8
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  let rootedBridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
  let revisionBridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt rootedBridge
  let execution :=
    sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
      revisionBridge
  fail_if_success exact
    (novelty : SourceGeneratedReflexiveSelfU8At
      (legislation execution) (exactRevolution execution)
        (exactConsumption execution))
  fail_if_success exact
    (rootedBridge.rightRootedFailure : SourceGeneratedReflexiveSelfU8At
      (legislation execution) (exactRevolution execution)
        (exactConsumption execution))
  fail_if_success exact
    (revisionBridge.rightCore : SourceGeneratedReflexiveSelfU8At
      (legislation execution) (exactRevolution execution)
        (exactConsumption execution))
  fail_if_success exact
    (execution.compilation : SourceGeneratedReflexiveSelfU8At
      (legislation execution) (exactRevolution execution)
        (exactConsumption execution))
  trivial

end
end M14ProofCarryingContributionCapacityCofinalNoveltySelfU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.proofCarryingContributionCapacityCofinalNoveltySelfU8
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.selfU8_sameOccurrenceAsRightPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCofinalNoveltySelfU8.bareNoveltyFragmentsCannotRetypeAsSelfU8
