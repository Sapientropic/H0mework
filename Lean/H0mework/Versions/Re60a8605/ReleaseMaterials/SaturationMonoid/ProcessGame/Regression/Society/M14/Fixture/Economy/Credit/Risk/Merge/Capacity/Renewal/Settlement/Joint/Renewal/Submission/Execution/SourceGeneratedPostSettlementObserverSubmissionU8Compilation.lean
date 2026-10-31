import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Revision.SourceGeneratedPostSettlementObserverSubmissionFirstRowU8Revision
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# Exact old-root compilation of the observer-submission U8 core

The cofinal right replay fixes one literal joint-root Payment visit.  The
inherited inquiry coordinate at that visit compiles the established richer U8
core after its source was augmented with the observer-submission renewal face.
The compiler accepts no revised root, row, material, core or result branch.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverSubmissionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8Revision
open M14SourceGeneratedContributionMergeActionSource

def failureFrontierAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8Revision.frontierAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

@[simp] theorem failureFrontier_rooted_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (failureFrontierAt oldVisit sourceIndex boundary).rooted =
      rootedFailureAt oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem failureFrontier_coface_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (failureFrontierAt oldVisit sourceIndex boundary).coface =
      canonicalCofaceAt oldVisit sourceIndex boundary :=
  rfl

def realizationCandidateAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationAt
      (failureFrontierAt oldVisit sourceIndex boundary) where
  NewV := NewVAt oldVisit sourceIndex boundary
  source := revisedLedgerSourceAt oldVisit sourceIndex boundary

def generatedU8CoreAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedInquiryU8RevisionCoreAt jointRoot
      (.finite (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (M9ProofCarryingRenewalU8Revision.inquiryEventAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.entry
      (M9ProofCarryingRenewalU8Failure.authorityAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      RootInquiryU8CompletionRegression.obstruction
      RootInquiryU8CompletionRegression.u7Gate
      RootInquiryU8CompletionRegression.failure where
  frontier := failureFrontierAt oldVisit sourceIndex boundary
  revision := typedRevisionSourceAt oldVisit sourceIndex boundary

theorem realizationCertificationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationCertificationAt
      (realizationCandidateAt oldVisit sourceIndex boundary)
      (generatedU8CoreAt oldVisit sourceIndex boundary) where
  frontier_eq := rfl
  source_heq := HEq.rfl

def sourceCompilationAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
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
    (generatedU8CoreAt oldVisit sourceIndex boundary)

def sourceCompilationProgramAt (oldVisit : OldVisit)
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
    sourceCompilationAt oldVisit sourceIndex boundary

def sourceGeneratedCompilationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  (sourceCompilationProgramAt oldVisit sourceIndex boundary).generate

def sourceCompilationFaceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeRootInquiryCompilationFaceCoreAt jointRoot
      (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) ()
      (M9ProofCarryingRenewalU8Revision.inquiryEventAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      M9ProofCarryingRenewalU8Failure.entry
      (M9ProofCarryingRenewalU8Failure.authorityAt
        (oldRootVisitAt oldVisit sourceIndex boundary))
      (sourceGeneratedCompilationAt oldVisit sourceIndex boundary).output where
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

def sourceInquiryStateAt (oldVisit : OldVisit)
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
    sourceCompilationProgramAt oldVisit sourceIndex boundary
  compilationFaceAt := fun _ =>
    sourceCompilationFaceAt oldVisit sourceIndex boundary
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq
    exact M9ProofCarryingRenewalU8Failure.theoryAuditRootDispositionCommutesAt
      (oldRootVisitAt oldVisit sourceIndex boundary)

def sourcePresentationAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RootInquiryStatePresentation where
  N := M9ProofCarryingRenewalInquiryRoot.N
  V := M9ProofCarryingRenewalInquiryRoot.V
  state := RootInquiryEngineStateAt.create
    (sourceInquiryStateAt oldVisit sourceIndex boundary)

@[simp] theorem sourceGeneratedOutput_exact (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (sourceGeneratedCompilationAt oldVisit sourceIndex boundary).output =
      sourceCompilationAt oldVisit sourceIndex boundary :=
  rfl

theorem installedCompilation_factorizes (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    let generated := jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary))
    HEq
      (jointRoot.toAuthoritativeRoot.source.projectionLaw.project
        (sourceCompilationFaceAt oldVisit sourceIndex boundary).projection
        generated.occurrence
        (sourceCompilationFaceAt oldVisit sourceIndex boundary).active)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := M9ProofCarryingRenewalU8Failure.entry) (query := ())
        (event := M9ProofCarryingRenewalU8Revision.inquiryEventAt
          (oldRootVisitAt oldVisit sourceIndex boundary))
        (audit := (sourceCompilationAt oldVisit sourceIndex boundary).audit)
        (sourceCompilationAt oldVisit sourceIndex boundary).answerReadout) :=
  (sourceCompilationFaceAt oldVisit sourceIndex boundary).project_heq

theorem exactProblemOccurrence_isRightPaymentOccurrence
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (oldRootVisitAt oldVisit sourceIndex boundary)) =
      ((rightReplayAt oldVisit sourceIndex boundary).2.futureBirth.actualExit
        ).paymentOccurrence.rootOccurrence :=
  rightPaymentRootOccurrence_exact oldVisit sourceIndex boundary |>.symm

theorem outputContainsNoSiblingCore (oldVisit : OldVisit)
    (sourceIndex boundary : Nat)
    (other : SourceGeneratedInquiryCompilationAt
      (sourceCompilationProgramAt oldVisit sourceIndex boundary)) :
    other.output =
      (sourceGeneratedCompilationAt oldVisit sourceIndex boundary).output :=
  other.output_eq (sourceGeneratedCompilationAt oldVisit sourceIndex boundary)

end
end M14SourceGeneratedPostSettlementObserverSubmissionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.generatedU8CoreAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.installedCompilation_factorizes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.outputContainsNoSiblingCore
