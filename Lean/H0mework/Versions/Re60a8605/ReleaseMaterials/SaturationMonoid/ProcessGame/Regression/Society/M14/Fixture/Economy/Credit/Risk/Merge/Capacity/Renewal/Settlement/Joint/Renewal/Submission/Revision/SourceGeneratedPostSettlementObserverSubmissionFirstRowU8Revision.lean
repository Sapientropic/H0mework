import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Root.SourceInstalledPostSettlementObserverSubmissionRevisedRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Revision

/-!
# Observer-submission augmentation of the richer M9 U8 revision

The generated typed revision retains the established loss-allocation network,
compiler-selected split, whole-ledger rows and canonical coface factorization.
Only its living authority source is replaced by the pre-emitter augmented
source.  The submission therefore occupies a dependent face of the same first
row; it does not generate the obstruction row or a sibling U8 core.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverSubmissionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring
open Renewal UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource

def baseGeneratedTypedRevisionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8RevisedWorld.generatedTypedRevisionAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

/-- Clone of the established richer occurrence with only the already
pre-emitter-augmented living authority source substituted. -/
def generatedTypedRevisionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    GeneratedTypedSemanticWorldNetworkRevisionAt
      (rootedFailureAt oldVisit sourceIndex boundary) where
  NewN := (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary).NewN
  translation :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary).translation
  NewV := (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary).NewV
  newLivingRoot := revisedLivingRootAt oldVisit sourceIndex boundary
  new_support_restricts :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).new_support_restricts
  oldTargetOpenLedger :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).oldTargetOpenLedger
  oldTargetOpenClaim_commutes :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).oldTargetOpenClaim_commutes
  oldTargetOpenProgressBudget_not_refilled :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).oldTargetOpenProgressBudget_not_refilled
  occurrencePresentation :=
    augmentedRevisedOccurrencePresentationAt oldVisit sourceIndex boundary
  occurrence_commutes :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).occurrence_commutes
  firstWrite := augmentedRevisedFirstWriteAt oldVisit sourceIndex boundary
  newOnlyEntry :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary).newOnlyEntry
  newOnlyProgressBudget_eq_zero :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).newOnlyProgressBudget_eq_zero
  revisedClaimHolds :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).revisedClaimHolds
  semanticChange :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary).semanticChange
  revisedClaim_hasNoOldPreimage :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).revisedClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).newOnlyIncidence_hasNoOldPreimage
  oldEntryRows :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary).oldEntryRows
  newOnlyEntry_hasNoOldPreimage :=
    (baseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).newOnlyEntry_hasNoOldPreimage
  newOnlyEntryRow := augmentedNewEntryRowAt oldVisit sourceIndex boundary

def generatedFirstSuccessorAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      (generatedTypedRevisionAt oldVisit sourceIndex boundary
        ).initialRestructuringGenerated.occurrence
      (generatedTypedRevisionAt oldVisit sourceIndex boundary
        ).initialRestructuringGenerated.wholeLedgerWriteBack :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedFirstSuccessorAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def augmentedGeneratedFirstWriteGenuineSplitAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (generatedTypedRevisionAt oldVisit sourceIndex boundary
      ).SourceGeneratedFirstWriteGenuineSplitAt :=
  let visit := oldRootVisitAt oldVisit sourceIndex boundary
  GeneratedTypedSemanticWorldNetworkRevisionAt.SourceGeneratedFirstWriteGenuineSplitAt.ofCompilerSelectedSplit
      (generatedTypedRevisionAt oldVisit sourceIndex boundary)
      (generatedFirstSuccessorAt oldVisit sourceIndex boundary)
      (M9ProofCarryingRenewalU8RevisedLedger.revisedLossChildAAt visit)
      (M9ProofCarryingRenewalU8RevisedLedger.revisedLossChildBAt visit)
      (M14SourceGeneratedLossAllocationWorld.lossAllocationChildren_distinct
        (rootedAt visit))
      (M14SourceGeneratedLossAllocationRestructuring.lossAllocationFirstOriginEq
        (rootedAt visit)
        (M9ProofCarryingRenewalU8RevisedLedger.revisedEmittedAt visit 0))
      rfl
      (M9ProofCarryingRenewalU8RevisedLedger.revisedFirstSplitCoverageAt visit)
      (M9ProofCarryingRenewalU8RevisedLedger.revisedFirstCompiler_selects_exact_split_at
        visit)
      (by
        intro entry
        rcases M14SourceGeneratedLossAllocationRestructuring.lossAllocationInitialEntry_cases
            (rootedAt visit) entry with
          entry_eq | entry_eq
        · subst entry
          exact .inl ⟨⟨(rootedAt visit).oldTargetEntry, PLift.up rfl⟩⟩
        · subst entry
          exact .inr rfl)
      (by
        intro targetEntry
        rcases M14SourceGeneratedLossAllocationRestructuring.lossAllocationTargetEntry_cases
            (rootedAt visit) targetEntry with
          target_eq | target_eq | target_eq
        · subst targetEntry
          exact .inl ⟨⟨(rootedAt visit).oldTargetEntry, PLift.up rfl⟩⟩
        · subst targetEntry
          exact .inl ⟨⟨(rootedAt visit).oldTargetEntry, PLift.up rfl⟩⟩
        · subst targetEntry
          exact .inr rfl)

theorem generatedTypedRevision_richerGroundingAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (generatedTypedRevisionAt oldVisit sourceIndex boundary
      ).SourceGeneratedFaithfulRicherCofaceRestructuringAt where
  lawSurface_heq := HEq.rfl
  genuineFirstWriteSplit :=
    ⟨augmentedGeneratedFirstWriteGenuineSplitAt oldVisit sourceIndex
      boundary⟩

/-- The established loss-allocation action, re-grounded on the augmented
revision itself.  Its successor and children are the existing compiler output;
only the revision authority now also carries the observer-submission face. -/
def augmentedDefaultSideLossAllocationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceGeneratedDefaultSideLossAllocationAt
      (generatedTypedRevisionAt oldVisit sourceIndex boundary) :=
  SourceGeneratedDefaultSideLossAllocationAt.ofGroundedFirstWriteSplit
    (generatedTypedRevisionAt oldVisit sourceIndex boundary)
    (augmentedGeneratedFirstWriteGenuineSplitAt oldVisit sourceIndex boundary)
    HEq.rfl
    (M9ProofCarryingRenewalU8RevisedWorld.generatedFirstWrite_children_bearers_distinct_at
      (oldRootVisitAt oldVisit sourceIndex boundary))

def typedRevisionSourceAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt
      (rootedFailureAt oldVisit sourceIndex boundary) :=
  (augmentedDefaultSideLossAllocationAt oldVisit sourceIndex boundary
    ).fieldGroundedRevision

@[simp] theorem augmentedDefaultSideLossAllocation_groundsTypedRevision
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (augmentedDefaultSideLossAllocationAt oldVisit sourceIndex boundary
      ).fieldGroundedRevision =
      typedRevisionSourceAt oldVisit sourceIndex boundary :=
  rfl

def augmentedFailureFrontierAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8Revision.frontierAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def augmentedRealizationCandidateAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationAt
      (augmentedFailureFrontierAt oldVisit sourceIndex boundary) :=
  SourceNativeInquiryCofaceRealizationAt.ofGeneratedRevision
    (generatedTypedRevisionAt oldVisit sourceIndex boundary)

def augmentedU8CoreAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
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
  frontier := augmentedFailureFrontierAt oldVisit sourceIndex boundary
  revision := typedRevisionSourceAt oldVisit sourceIndex boundary

theorem augmentedRealizationCertificationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationCertificationAt
      (augmentedRealizationCandidateAt oldVisit sourceIndex boundary)
      (augmentedU8CoreAt oldVisit sourceIndex boundary) where
  frontier_eq := rfl
  source_heq := HEq.rfl

@[simp] theorem submissionFace_sourceEntry_eq_newOnlyEntry
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.sourceEntry =
      (generatedTypedRevisionAt oldVisit sourceIndex boundary).newOnlyEntry :=
  rfl

theorem submissionFace_selectedRow_heq_generatedNewOnlyRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (activatedSubmissionAt oldVisit sourceIndex boundary).payload.selectedRow
      (generatedTypedRevisionAt oldVisit sourceIndex boundary
        ).newOnlyEntryRow.sourceRow :=
  HEq.rfl

theorem submissionFace_successor_heq_generatedSuccessor
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (activatedSubmissionAt oldVisit sourceIndex boundary).payload.successor
      (generatedFirstSuccessorAt oldVisit sourceIndex boundary) :=
  HEq.rfl

theorem activatedSubmission_completeFirstRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
        ((revisedLivingRootAt oldVisit sourceIndex boundary
          ).toAuthoritativeRoot.source.projectionLaw.outcomeAt
            (renewalRecognitionAt oldVisit sourceIndex boundary).rootProjection
            ((revisedLivingRootAt oldVisit sourceIndex boundary).emitted
              (0 : Nat)))
        ((renewalRecognitionAt oldVisit sourceIndex boundary).law.toProjectionLaw.outcomeAt
          PUnit.unit
            ((revisedLivingRootAt oldVisit sourceIndex boundary).emitted
              (0 : Nat))) ∧
      (activatedSubmissionAt oldVisit sourceIndex boundary).payload.sourceEntry =
        (generatedTypedRevisionAt oldVisit sourceIndex boundary).newOnlyEntry ∧
      HEq
        (activatedSubmissionAt oldVisit sourceIndex boundary).payload.selectedRow
        (generatedTypedRevisionAt oldVisit sourceIndex boundary
          ).newOnlyEntryRow.sourceRow ∧
      HEq
        (activatedSubmissionAt oldVisit sourceIndex boundary).payload.successor
        (generatedFirstSuccessorAt oldVisit sourceIndex boundary) ∧
      Nonempty
        (SourceNativeObserverConsumerRootedAuthorityAt
          (canonicalSubmissionAt oldVisit sourceIndex boundary)) :=
  ⟨actualFirstEvent_projectionOutcome_heq_sourceLaw oldVisit sourceIndex
      boundary,
    submissionFace_sourceEntry_eq_newOnlyEntry oldVisit sourceIndex boundary,
    submissionFace_selectedRow_heq_generatedNewOnlyRow oldVisit sourceIndex
      boundary,
    submissionFace_successor_heq_generatedSuccessor oldVisit sourceIndex
      boundary,
    augmentedInstalledPayload_carriesRootedAuthority oldVisit sourceIndex
      boundary⟩

end
end M14SourceGeneratedPostSettlementObserverSubmissionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.generatedTypedRevisionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.generatedTypedRevision_richerGroundingAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedU8CoreAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedRealizationCertificationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.activatedSubmission_completeFirstRow
