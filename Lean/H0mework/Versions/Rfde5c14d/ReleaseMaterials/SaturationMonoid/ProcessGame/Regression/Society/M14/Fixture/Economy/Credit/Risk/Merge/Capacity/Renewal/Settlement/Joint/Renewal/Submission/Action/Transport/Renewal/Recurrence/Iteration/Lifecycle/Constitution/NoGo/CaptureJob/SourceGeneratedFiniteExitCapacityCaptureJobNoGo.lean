import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Producer.SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.NoGo.SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Celebration.Bearer.Execution.Producer.SourceGeneratedContributionCapacityBearerLeaveExecution

/-!
# Capture and Job-Guarantee separation for the finite exit constitution

Full capture leaves the existing paid lifecycle, bare future, services,
external responsibility and self-U8 successor in place, but makes the exact
bearer program's semantic exit renewal empty.  Job Guarantee remains a
separate role-conditioned standing: the ended employment relation cannot
generate it, while the existing `.newJob` seed for the same `.t1` worker can.

This file introduces no exit program, root, occurrence, registry or future
table.  Every cycle statement is generated on demand from the input cycle.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Observer UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open Lifecycle.Universal.FixedAdapter
open M14UBIExitCapacityFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerLeaveExecution
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPaidExitLifecycleMaximumNoGo
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution

/-! ## Exact semantic capture no-go -/

theorem birthBearerCapturedExitCapacityRenewal_isEmpty :
    IsEmpty (ExitCapacityRenewalAt birthBearerCapturedProgram) :=
  birthBearerNominalTransfer.excludes_exitCapacityRenewal

/-! ## Same-worker Job-Guarantee separation -/

/-- The existing employment relation has no target future at all. -/
theorem birthBearerEmploymentTargetFuture_empty :
    birthBearerExitRelationCompiler.futureCodesAt
        birthBearerEmploymentRelation .target = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro code member
  have generated :=
    (birthBearerExitRelationCompiler.mem_futureCodesAt_iff
      birthBearerEmploymentRelation .target code).mp member
  exact nomatch Classical.choice generated.2

abbrev BirthBearerEmploymentJobGuaranteeStanding :=
  JobGuaranteeStandingAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (exitRelationCompiler := birthBearerExitRelationCompiler)
    birthBearerWorker birthBearerEmploymentRelation
      (birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
        .target)

theorem birthBearerEmploymentJobGuarantee_isEmpty :
    IsEmpty BirthBearerEmploymentJobGuaranteeStanding :=
  noEmploymentTargetFuture_noJobGuarantee
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (exitRelationCompiler := birthBearerExitRelationCompiler)
    birthBearerWorker birthBearerEmploymentRelation
      (birthBearerExitRelationCompiler.roleAt birthBearerEmploymentRelation
        .target)
    birthBearerEmploymentTargetFuture_empty

/-- The alternative job consumes the `.newJob` relation already emitted by
the bearer leave-execution producer. -/
theorem birthBearerNewJobInterest :
    birthBearerExitRelationCompiler.GeneratedInterestAt
      birthBearerWorker birthBearerNewJobRelation :=
  ⟨birthBearerExactRelationSeed .newJob, rfl, rfl⟩

theorem birthBearerNewJobWork_target_actionable :
    ActionableAt birthBearerExitRelationCompiler.futureIdle
      (birthBearerExitRelationCompiler.futureCodesAt
        birthBearerNewJobRelation .target) .work := by
  constructor
  · apply
      (birthBearerExitRelationCompiler.mem_futureCodesAt_iff
        birthBearerNewJobRelation .target .work).mpr
    exact ⟨by
      change ExitFutureCode.work ∈
        ({.idle, .work, .leave} : Finset ExitFutureCode)
      simp, ⟨PUnit.unit⟩⟩
  · simp [birthBearerExitRelationCompiler]

abbrev BirthBearerNewJobGuaranteeStanding :=
  JobGuaranteeStandingAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (exitRelationCompiler := birthBearerExitRelationCompiler)
    birthBearerWorker birthBearerNewJobRelation
      (birthBearerExitRelationCompiler.roleAt birthBearerNewJobRelation .target)

def birthBearerNewJobGuaranteeStanding :
    BirthBearerNewJobGuaranteeStanding where
  roleAuthority := ⟨birthBearerNewJobInterest, rfl⟩
  workCode := .work
  workActionable := birthBearerNewJobWork_target_actionable

theorem birthBearerPositiveExitAndJobGuarantee_coexist :
    Nonempty (ExitCapacityRenewalAt birthBearerExitCapacityProgram) ∧
      Nonempty BirthBearerNewJobGuaranteeStanding :=
  ⟨⟨semanticExitCapacityRenewal⟩,
    ⟨birthBearerNewJobGuaranteeStanding⟩⟩

theorem birthBearerCapturedNoExitAndJobGuarantee_coexist :
    IsEmpty (ExitCapacityRenewalAt birthBearerCapturedProgram) ∧
      Nonempty BirthBearerNewJobGuaranteeStanding :=
  ⟨birthBearerCapturedExitCapacityRenewal_isEmpty,
    ⟨birthBearerNewJobGuaranteeStanding⟩⟩

/-- Role-conditioned employment support is not the logical complement of the
independent UBI exit: both are inhabited in the positive source program. -/
theorem birthBearerJobGuarantee_isNotComplementOfPositiveExit :
    ¬ (Nonempty BirthBearerNewJobGuaranteeStanding ↔
      IsEmpty (ExitCapacityRenewalAt birthBearerExitCapacityProgram)) := by
  intro complement
  exact (complement.mp ⟨birthBearerNewJobGuaranteeStanding⟩).false
    semanticExitCapacityRenewal

/-! ## Full-capture counterlife at one recursively generated cycle -/

structure FiniteExitCapacityFullCaptureCounterlifeAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  positiveConstitution : FiniteExitCapacityConstitutionAt initial depth
  fullCaptureCounterlife : Nonempty
    (ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth))
  capturedSemanticNoExit :
    IsEmpty (ExitCapacityRenewalAt birthBearerCapturedProgram)
  capturedNominal : NominalTransferReadoutAt birthBearerCapturedProgram
  capturedGeometryRenewalEmpty : IsEmpty
    (birthBearerCapturedGeometryCompilerAt
      (cycleExitCapacityDepthAt initial depth)
    ).SourceGeneratedActionableExitRenewalAt
  capturedProgramAxesExact :
    birthBearerCapturedProgram.purchasingPowerStanding =
        birthBearerExitCapacityProgram.purchasingPowerStanding ∧
      birthBearerCapturedProgram.employmentLoss =
        birthBearerExitCapacityProgram.employmentLoss ∧
      birthBearerCapturedProgram.exitInterest =
        birthBearerExitCapacityProgram.exitInterest
  capturedPaymentExact :
    birthBearerCapturedProgram.payment =
      birthBearerExitCapacityProgram.payment
  bareRoleIndependentFuture : Nonempty
    (birthBearerExitRelationCompiler.FutureContinuationAt
      birthBearerIndependentExitRelation.1 .target
      (cycleLifecycleMaximum initial depth
        ).continuation.successorContinuationAction.1)
  actualPaymentSpine : PaidExitLifecycleOccurrenceSpineAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)
  cyclePaymentExact :
    (cycleLifecycle initial depth
      ).sourceConsequence.actualExit.paymentOccurrence =
      targetPaymentOccurrence
        (legislationSpan (cycleMorphism (cycleAt initial depth)))
  servicesAndFuture : PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)
  externalResidual : PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)
  sourceResidualOwned :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership
  rootResidualConsumer : Nonempty
    (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
      (cycleLifecycleMaximum initial depth
        ).continuation.paidContinuationStep.targetCurrent.actualExit)
  selfU8 :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism (cycleAt initial depth))
  selfU8CoreExact :
    targetCore (cycleMorphism (cycleAt initial depth)) =
      generatedU8CoreAt oldVisit sourceIndex (boundary + depth)
  generatedNextCycle :
    cycleAt initial (depth + 1) = (stepAt initial depth).nextCycle
  generatedNextSelfU8 :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism (cycleAt initial (depth + 1)))

theorem sourceGeneratedFiniteExitCapacityFullCaptureCounterlifeAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    FiniteExitCapacityFullCaptureCounterlifeAt initial depth := by
  let constitution := sourceGeneratedFiniteExitCapacityConstitutionAt
    initial depth
  let counterlife := cycleFullCaptureCounterlifeAt initial depth
  exact
    { positiveConstitution := constitution
      fullCaptureCounterlife := ⟨counterlife⟩
      capturedSemanticNoExit :=
        birthBearerCapturedExitCapacityRenewal_isEmpty
      capturedNominal := counterlife.nominalTransfer
      capturedGeometryRenewalEmpty := counterlife.capturedRenewalEmpty
      capturedProgramAxesExact :=
        ⟨counterlife.continuationCountermodel.installedPaymentAxisExact,
          counterlife.continuationCountermodel.installedEmploymentAxisExact,
          counterlife.continuationCountermodel.installedExitInterestAxisExact⟩
      capturedPaymentExact := rfl
      bareRoleIndependentFuture := by
        rw [← cycleFullCaptureCounterlife_positive_isCycleMaximum initial depth]
        exact ⟨counterlife.continuationCountermodel.bareFuture⟩
      actualPaymentSpine := counterlife.occurrenceSpinePreserved
      cyclePaymentExact := constitution.actualPaymentExact
      servicesAndFuture := counterlife.servicesAndFuturePreserved
      externalResidual := counterlife.externalDispositionPreserved
      sourceResidualOwned :=
        counterlife.externalDispositionPreserved.sourceOwnedResidual
      rootResidualConsumer :=
        counterlife.externalDispositionPreserved.rootConsumer
      selfU8 := constitution.selfU8
      selfU8CoreExact := constitution.selfU8CoreExact
      generatedNextCycle := constitution.generatedNextCycle
      generatedNextSelfU8 :=
        cycleMorphismCertificate (cycleAt initial (depth + 1)) }

/-! ## Direct bounded no-go mouth -/

structure FiniteExitCapacityCaptureJobNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  fullCapture : FiniteExitCapacityFullCaptureCounterlifeAt initial depth
  endedEmploymentJobGuaranteeEmpty :
    IsEmpty BirthBearerEmploymentJobGuaranteeStanding
  newJobGuaranteeExists : Nonempty BirthBearerNewJobGuaranteeStanding
  positiveCoexistence :
    Nonempty (ExitCapacityRenewalAt birthBearerExitCapacityProgram) ∧
      Nonempty BirthBearerNewJobGuaranteeStanding
  capturedCoexistence :
    IsEmpty (ExitCapacityRenewalAt birthBearerCapturedProgram) ∧
      Nonempty BirthBearerNewJobGuaranteeStanding
  notComplements :
    ¬ (Nonempty BirthBearerNewJobGuaranteeStanding ↔
      IsEmpty (ExitCapacityRenewalAt birthBearerExitCapacityProgram))

theorem sourceGeneratedFiniteExitCapacityCaptureJobNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    FiniteExitCapacityCaptureJobNoGoAt initial depth where
  fullCapture :=
    sourceGeneratedFiniteExitCapacityFullCaptureCounterlifeAt initial depth
  endedEmploymentJobGuaranteeEmpty :=
    birthBearerEmploymentJobGuarantee_isEmpty
  newJobGuaranteeExists := ⟨birthBearerNewJobGuaranteeStanding⟩
  positiveCoexistence := birthBearerPositiveExitAndJobGuarantee_coexist
  capturedCoexistence := birthBearerCapturedNoExitAndJobGuarantee_coexist
  notComplements := birthBearerJobGuarantee_isNotComplementOfPositiveExit

end
end M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo.birthBearerCapturedExitCapacityRenewal_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo.birthBearerEmploymentJobGuarantee_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo.birthBearerPositiveExitAndJobGuarantee_coexist
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo.birthBearerJobGuarantee_isNotComplementOfPositiveExit
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo.sourceGeneratedFiniteExitCapacityFullCaptureCounterlifeAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo.sourceGeneratedFiniteExitCapacityCaptureJobNoGoAt
