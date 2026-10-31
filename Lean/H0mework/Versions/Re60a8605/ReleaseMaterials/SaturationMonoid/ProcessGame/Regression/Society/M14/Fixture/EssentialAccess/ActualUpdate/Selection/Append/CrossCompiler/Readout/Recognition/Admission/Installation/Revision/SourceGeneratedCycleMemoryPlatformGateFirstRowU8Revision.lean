import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Installation.Root.SourceInstalledCycleMemoryPlatformGateRevisedRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Revision

/-!
# Cycle-memory platform gate in the existing first-row U8 revision

The established observer-submission revision is re-grounded with the richer
living root that also carries the source-generated platform-gate face.  No
network, vocabulary, occurrence presentation, ledger row, first write,
successor or loss-allocation child is replaced.  The existing rooted failure
continues to generate one exact U8 revision whose first row now also carries
the platform-channel admission.  The platform carrier no-go generates this
dependent face; it is not claimed to generate the pre-existing U7/coface.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGateU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring
open Renewal UniversalRootGrammar
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedCycleMemoryPlatformGateObstruction
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransport

def platformGateBaseGeneratedTypedRevisionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  M14SourceGeneratedPostSettlementObserverSubmissionU8.generatedTypedRevisionAt
    oldVisit sourceIndex boundary

/-- The existing generated revision with only its living root replaced by the
definitionally same restructuring source carrying one additional face. -/
def platformGateGeneratedTypedRevisionAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    GeneratedTypedSemanticWorldNetworkRevisionAt
      (rootedFailureAt oldVisit sourceIndex boundary) where
  NewN :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).NewN
  translation :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).translation
  NewV :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).NewV
  newLivingRoot :=
    platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
  new_support_restricts :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).new_support_restricts
  oldTargetOpenLedger :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).oldTargetOpenLedger
  oldTargetOpenClaim_commutes :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).oldTargetOpenClaim_commutes
  oldTargetOpenProgressBudget_not_refilled :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).oldTargetOpenProgressBudget_not_refilled
  occurrencePresentation :=
    platformGateRevisedOccurrencePresentationAt oldVisit sourceIndex boundary
  occurrence_commutes :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).occurrence_commutes
  firstWrite :=
    platformGateRevisedFirstWriteAt oldVisit sourceIndex boundary
  newOnlyEntry :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).newOnlyEntry
  newOnlyProgressBudget_eq_zero :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).newOnlyProgressBudget_eq_zero
  revisedClaimHolds :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).revisedClaimHolds
  semanticChange :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).semanticChange
  revisedClaim_hasNoOldPreimage :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).revisedClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).newOnlyIncidence_hasNoOldPreimage
  oldEntryRows :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).oldEntryRows
  newOnlyEntry_hasNoOldPreimage :=
    (platformGateBaseGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).newOnlyEntry_hasNoOldPreimage
  newOnlyEntryRow :=
    platformGateNewEntryRowAt oldVisit sourceIndex boundary

def platformGateGeneratedFirstSuccessorAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
        ).initialRestructuringGenerated.occurrence
      (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
        ).initialRestructuringGenerated.wholeLedgerWriteBack :=
  M9ProofCarryingRenewalU8RevisedWorld.revisedFirstSuccessorAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateGeneratedFirstWriteGenuineSplitAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).SourceGeneratedFirstWriteGenuineSplitAt :=
  let visit := oldRootVisitAt oldVisit sourceIndex boundary
  GeneratedTypedSemanticWorldNetworkRevisionAt.SourceGeneratedFirstWriteGenuineSplitAt.ofCompilerSelectedSplit
      (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary)
      (platformGateGeneratedFirstSuccessorAt oldVisit sourceIndex boundary)
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

theorem platformGateGeneratedTypedRevision_richerGroundingAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
      ).SourceGeneratedFaithfulRicherCofaceRestructuringAt where
  lawSurface_heq := HEq.rfl
  genuineFirstWriteSplit :=
    ⟨platformGateGeneratedFirstWriteGenuineSplitAt oldVisit sourceIndex
      boundary⟩

def platformGateDefaultSideLossAllocationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceGeneratedDefaultSideLossAllocationAt
      (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary) :=
  SourceGeneratedDefaultSideLossAllocationAt.ofGroundedFirstWriteSplit
    (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary)
    (platformGateGeneratedFirstWriteGenuineSplitAt oldVisit sourceIndex
      boundary)
    HEq.rfl
    (M9ProofCarryingRenewalU8RevisedWorld.generatedFirstWrite_children_bearers_distinct_at
      (oldRootVisitAt oldVisit sourceIndex boundary))

def platformGateTypedRevisionSourceAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt
      (rootedFailureAt oldVisit sourceIndex boundary) :=
  (platformGateDefaultSideLossAllocationAt oldVisit sourceIndex boundary
    ).fieldGroundedRevision

def platformGateFailureFrontierAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  M9ProofCarryingRenewalU8Revision.frontierAt
    (oldRootVisitAt oldVisit sourceIndex boundary)

def platformGateRealizationCandidateAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationAt
      (platformGateFailureFrontierAt oldVisit sourceIndex boundary) :=
  SourceNativeInquiryCofaceRealizationAt.ofGeneratedRevision
    (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary)

def platformGateU8CoreAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
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
  frontier := platformGateFailureFrontierAt oldVisit sourceIndex boundary
  revision := platformGateTypedRevisionSourceAt oldVisit sourceIndex boundary

theorem platformGateRealizationCertificationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationCertificationAt
      (platformGateRealizationCandidateAt oldVisit sourceIndex boundary)
      (platformGateU8CoreAt oldVisit sourceIndex boundary) where
  frontier_eq := rfl
  source_heq := HEq.rfl

@[simp] theorem platformGateFace_sourceEntry_eq_newOnlyEntry
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
      ).payload.sourceEntry =
      (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
        ).newOnlyEntry :=
  rfl

theorem platformGateFace_selectedRow_heq_generatedNewOnlyRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
        ).payload.selectedRow
      (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
        ).newOnlyEntryRow.sourceRow :=
  HEq.rfl

theorem platformGateFace_successor_heq_generatedSuccessor
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
        ).payload.successor
      (platformGateGeneratedFirstSuccessorAt oldVisit sourceIndex boundary) :=
  HEq.rfl

/-- Exact paid update: same occurrence, first row, successor and U8 core now
carry the cofinal memory obstruction, the new platform-channel candidate and
the previously installed observer-submission authority. -/
theorem platformGateU8_completeFirstRow (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    type_of% (platformGateGeneratedTypedRevision_richerGroundingAt oldVisit
      sourceIndex boundary) ∧
      type_of% (platformGateRealizationCertificationAt oldVisit sourceIndex
        boundary) ∧
      (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
        ).payload.sourceEntry =
        (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
          ).newOnlyEntry ∧
      HEq
        (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
          ).payload.selectedRow
        (platformGateGeneratedTypedRevisionAt oldVisit sourceIndex boundary
          ).newOnlyEntryRow.sourceRow ∧
      HEq
        (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
          ).payload.successor
        (platformGateGeneratedFirstSuccessorAt oldVisit sourceIndex boundary) ∧
      Nonempty
        (SourceGeneratedCycleMemoryPlatformGatePaymentLineageTransportAt
          oldVisit sourceIndex boundary) ∧
      Nonempty
        (SourceGeneratedPlatformChannelRevisionCandidateAt boundary) ∧
      Nonempty
        (SourceNativeObserverConsumerRootedAuthorityAt
          (canonicalSubmissionAt oldVisit sourceIndex boundary)) :=
  ⟨platformGateGeneratedTypedRevision_richerGroundingAt oldVisit
      sourceIndex boundary,
    platformGateRealizationCertificationAt oldVisit sourceIndex boundary,
    platformGateFace_sourceEntry_eq_newOnlyEntry oldVisit sourceIndex boundary,
    platformGateFace_selectedRow_heq_generatedNewOnlyRow oldVisit sourceIndex
      boundary,
    platformGateFace_successor_heq_generatedSuccessor oldVisit sourceIndex
      boundary,
    platformGateInstalledPayload_carriesPaymentLineageTransport oldVisit sourceIndex
      boundary,
    platformGateInstalledPayload_carriesRevisionCandidate oldVisit sourceIndex
      boundary,
    inheritedSubmissionPayload_carriesRootedAuthority oldVisit sourceIndex
      boundary⟩

end
end M14SourceGeneratedCycleMemoryPlatformGateU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateGeneratedTypedRevisionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateGeneratedTypedRevision_richerGroundingAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateU8CoreAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRealizationCertificationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateU8_completeFirstRow
