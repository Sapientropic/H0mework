import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Installation.Revision.SourceGeneratedCycleMemoryPlatformGateFirstRowU8Revision
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Execution.SourceGeneratedPostSettlementObserverSubmissionU8Compilation

/-!
# Exact old-root compilation of the platform-gate U8 core

The literal joint-root Payment visit compiles the richer platform-gate core.
The source program accepts no revised root, row, core or result branch, so the
cycle-memory admission cannot be installed by a sibling execution.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGateU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8Revision
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8

def platformGateSourceCompilationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCompilationAt jointRoot
      (.finite (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (M9ProofCarryingRenewalU8Revision.inquiryEventAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.entry
      (M9ProofCarryingRenewalU8Failure.authorityAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) :=
  .requiresU8 RootInquiryU8CompletionRegression.obstruction
    RootInquiryU8CompletionRegression.u7Gate
    RootInquiryU8CompletionRegression.failure
    (platformGateU8CoreAt oldVisit sourceIndex boundary)

def platformGateSourceCompilationProgramAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCompilationProgramAt jointRoot
      (.finite (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (M9ProofCarryingRenewalU8Revision.inquiryEventAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.entry
      (M9ProofCarryingRenewalU8Failure.authorityAt
        (oldRootVisitAt oldVisit sourceIndex boundary)) where
  compile := fun _exactEvent =>
    platformGateSourceCompilationAt oldVisit sourceIndex boundary

def platformGateSourceGeneratedCompilationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  (platformGateSourceCompilationProgramAt oldVisit sourceIndex boundary
    ).generate

def platformGateSourceCompilationFaceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRootInquiryCompilationFaceCoreAt jointRoot
      (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) ()
      (M9ProofCarryingRenewalU8Revision.inquiryEventAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.entry
      (M9ProofCarryingRenewalU8Failure.authorityAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      (platformGateSourceGeneratedCompilationAt oldVisit sourceIndex boundary
        ).output where
  projection := jointInquiryProjection
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := by
    have outcome :=
      M9ProofCarryingRenewalInquiryRuntime.inheritedInquiryInstallation.outcome_heq
        (jointRoot.emitted
          (oldRootVisitAt oldVisit sourceIndex boundary).current) .inquiry
    cases outcome
    exact HEq.rfl

def platformGateSourceInquiryStateAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    RootInquiryStateAt M9ProofCarryingRenewalInquiryRoot.N
      M9ProofCarryingRenewalInquiryRoot.V where
  root := jointRoot
  visit := .finite (oldRootVisitAt oldVisit sourceIndex boundary)
  U7 := M9ProofCarryingRenewalU8Failure.U7
  calculus := RootInquiryU8CompletionRegression.theoryAuditCalculus
  Query := Unit
  entryAt := fun _ => M9ProofCarryingRenewalU8Failure.entry
  authorityAt := fun _ => M9ProofCarryingRenewalU8Failure.authorityAt
    (oldRootVisitAt oldVisit sourceIndex boundary)
  compilationProgramAt := fun _ =>
    platformGateSourceCompilationProgramAt oldVisit sourceIndex boundary
  compilationFaceAt := fun _ =>
    platformGateSourceCompilationFaceAt oldVisit sourceIndex boundary
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq
    exact M9ProofCarryingRenewalU8Failure.theoryAuditRootDispositionCommutesAt
      (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateSourcePresentationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) : RootInquiryStatePresentation where
  N := M9ProofCarryingRenewalInquiryRoot.N
  V := M9ProofCarryingRenewalInquiryRoot.V
  state := RootInquiryEngineStateAt.create
    (platformGateSourceInquiryStateAt oldVisit sourceIndex boundary)

@[simp] theorem platformGateSourceGeneratedOutput_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateSourceGeneratedCompilationAt oldVisit sourceIndex boundary
      ).output =
      platformGateSourceCompilationAt oldVisit sourceIndex boundary :=
  rfl

theorem platformGateInstalledCompilation_factorizes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let generated := jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary))
    HEq
      (jointRoot.toAuthoritativeRoot.source.projectionLaw.project
        (platformGateSourceCompilationFaceAt oldVisit sourceIndex boundary
          ).projection
        generated.occurrence
        (platformGateSourceCompilationFaceAt oldVisit sourceIndex boundary
          ).active)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := M9ProofCarryingRenewalU8Failure.entry) (query := ())
        (event := M9ProofCarryingRenewalU8Revision.inquiryEventAt
          (oldRootVisitAt oldVisit sourceIndex boundary))
        (audit :=
          (platformGateSourceCompilationAt oldVisit sourceIndex boundary
            ).audit)
        (platformGateSourceCompilationAt oldVisit sourceIndex boundary
          ).answerReadout) :=
  (platformGateSourceCompilationFaceAt oldVisit sourceIndex boundary
    ).project_heq

theorem platformGateExactProblemOccurrence_isRightPaymentOccurrence
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence.rootOccurrence :=
  exactProblemOccurrence_isRightPaymentOccurrence oldVisit sourceIndex boundary

theorem platformGateOutputContainsNoSiblingCore (oldVisit : OldVisit)
    (sourceIndex boundary : Nat)
    (other : SourceGeneratedInquiryCompilationAt
      (platformGateSourceCompilationProgramAt oldVisit sourceIndex boundary)) :
    other.output =
      (platformGateSourceGeneratedCompilationAt oldVisit sourceIndex boundary
        ).output :=
  other.output_eq
    (platformGateSourceGeneratedCompilationAt oldVisit sourceIndex boundary)

end
end M14SourceGeneratedCycleMemoryPlatformGateU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateSourceCompilationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateInstalledCompilation_factorizes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateOutputContainsNoSiblingCore
