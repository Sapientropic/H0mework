import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Root.SourceGeneratedContributionCapacityU8Root

/-!
# Source-generated contribution-capacity self-U8 revision

The capacity target's exact failure frontier emits one field-grounded typed
revision.  Its carrier is definitionally the canonical minimal coface, its
law surface is that coface's root semantics, and its first whole-ledger write
contains all inherited rows plus the generated residual row.  No sibling
revision, post-hoc attachment, or completed future is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8Revision

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open TypedSemanticWorldNetworkU8
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityFailure
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root

def generatedContributionCapacityTypedRevisionAt
    (oldVisit : OldVisit) :
    GeneratedTypedSemanticWorldNetworkRevisionAt
      (capacityRootedFailureAt oldVisit) where
  NewN := CapacityU8NAt oldVisit
  translation := (CapacityCofaceAt oldVisit).translation
  NewV := CapacityU8VAt oldVisit
  newLivingRoot := contributionCapacityU8LivingRoot oldVisit
  new_support_restricts :=
    (CapacityCofaceAt oldVisit).firstWrite_targetSupport_is_cofaceRestriction
  oldTargetOpenLedger := (CapacityCofaceAt oldVisit).cofaceLedgerRetract
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation := contributionCapacityU8OccurrencePresentation oldVisit
  occurrence_commutes := rfl
  firstWrite := contributionCapacityU8FirstWrite oldVisit
  newOnlyEntry := contributionCapacityU8GeneratedResidual oldVisit
  newOnlyProgressBudget_eq_zero := rfl
  revisedClaimHolds := (CapacityCofaceAt oldVisit).obstructionClaimHolds
  semanticChange := (CapacityCofaceAt oldVisit).obstructionSemanticChange
  revisedClaim_hasNoOldPreimage :=
    (CapacityCofaceAt oldVisit).obstructionClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage :=
    (CapacityCofaceAt oldVisit).obstructionIncidence_hasNoOldPreimage
  oldEntryRows := contributionCapacityU8OldEntryRows oldVisit
  newOnlyEntry_hasNoOldPreimage :=
    (CapacityCofaceAt oldVisit).obstructionEntry_hasNoOldPreimage
  newOnlyEntryRow := contributionCapacityU8GeneratedResidualRow oldVisit

theorem generatedContributionCapacityTypedRevision_exactGrounding
    (oldVisit : OldVisit) :
    (generatedContributionCapacityTypedRevisionAt oldVisit).ExactFieldGrounding where
  network_eq := rfl
  lawSurface_heq := HEq.rfl
  translation_heq := HEq.rfl
  initialSupport_heq := HEq.rfl
  oldTargetOpenLedger_heq := HEq.rfl
  newOnlyEntry_heq := HEq.rfl
  revisedClaimHolds_heq := HEq.rfl
  semanticChange_heq := HEq.rfl

def contributionCapacityFieldGroundedRevisionAt
    (oldVisit : OldVisit) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt
      (capacityRootedFailureAt oldVisit) :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofGeneratedOccurrence
    (generatedContributionCapacityTypedRevisionAt oldVisit)
    (generatedContributionCapacityTypedRevision_exactGrounding oldVisit)

/-! ## Exact failure frontier and one U8 core -/

def contributionCapacityFailureInquiryEventAt
    (oldVisit : OldVisit) :=
  ULift.up.{1, 0}
    ((CapacityRootAt oldVisit).emitted (CapacityVisitAt oldVisit).current)

def contributionCapacityFailureFrontierAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryCofaceFrontierAt
      (CapacityRootAt oldVisit) (CapacityVisitAt oldVisit)
      (contributionCapacityU7 (capacityActionRootedAt oldVisit))
      (contributionCapacityCalculus (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit)) ()
      (contributionCapacityFailureInquiryEventAt oldVisit)
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit))
      (contributionCapacityRootTargetObstructionAuthority
        (capacityActionRootedAt oldVisit))
      (contributionCapacityResidual (capacityActionRootedAt oldVisit))
      (contributionCapacityU7Gate (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalFailure
        (capacityActionRootedAt oldVisit)) :=
  SourceNativeInquiryCofaceFrontierAt.ofRootFailureFace
    (capacityFailureFaceAt oldVisit) rfl
    (capacityFailureSuccessorAt oldVisit)

@[simp] theorem contributionCapacityFailureFrontier_rooted_exact
    (oldVisit : OldVisit) :
    (contributionCapacityFailureFrontierAt oldVisit).rooted =
      capacityRootedFailureAt oldVisit :=
  rfl

@[simp] theorem contributionCapacityFailureFrontier_coface_exact
    (oldVisit : OldVisit) :
    (contributionCapacityFailureFrontierAt oldVisit).coface =
      CapacityCofaceAt oldVisit :=
  rfl

def contributionCapacityCofaceRealizationCandidateAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryCofaceRealizationAt
      (contributionCapacityFailureFrontierAt oldVisit) where
  NewV := CapacityU8VAt oldVisit
  source := (contributionCapacityU8RestructuringSource oldVisit).toLedgerSource

def generatedContributionCapacityU8CoreAt
    (oldVisit : OldVisit) :
    SourceGeneratedInquiryU8RevisionCoreAt
      (CapacityRootAt oldVisit) (CapacityVisitAt oldVisit)
      (contributionCapacityU7 (capacityActionRootedAt oldVisit))
      (contributionCapacityCalculus (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit)) ()
      (contributionCapacityFailureInquiryEventAt oldVisit)
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit))
      (contributionCapacityRootTargetObstructionAuthority
        (capacityActionRootedAt oldVisit))
      (contributionCapacityResidual (capacityActionRootedAt oldVisit))
      (contributionCapacityU7Gate (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalFailure
        (capacityActionRootedAt oldVisit)) where
  frontier := contributionCapacityFailureFrontierAt oldVisit
  revision := contributionCapacityFieldGroundedRevisionAt oldVisit

theorem contributionCapacityCofaceRealizationCertificationAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryCofaceRealizationCertificationAt
      (contributionCapacityCofaceRealizationCandidateAt oldVisit)
      (generatedContributionCapacityU8CoreAt oldVisit) where
  frontier_eq := rfl
  source_heq := HEq.rfl

def contributionCapacityRequiresU8CompilationAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryCompilationAt
      (CapacityRootAt oldVisit) (CapacityVisitAt oldVisit)
      (contributionCapacityU7 (capacityActionRootedAt oldVisit))
      (contributionCapacityCalculus (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit)) ()
      (contributionCapacityFailureInquiryEventAt oldVisit)
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit))
      (contributionCapacityRootTargetObstructionAuthority
        (capacityActionRootedAt oldVisit)) :=
  .requiresU8
    (contributionCapacityResidual (capacityActionRootedAt oldVisit))
    (contributionCapacityU7Gate (capacityActionRootedAt oldVisit))
    (contributionCapacityOperationalFailure (capacityActionRootedAt oldVisit))
    (generatedContributionCapacityU8CoreAt oldVisit)

def contributionCapacityRequiresU8CompilationProgramAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryCompilationProgramAt
      (CapacityRootAt oldVisit) (CapacityVisitAt oldVisit)
      (contributionCapacityU7 (capacityActionRootedAt oldVisit))
      (contributionCapacityCalculus (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit)) ()
      (contributionCapacityFailureInquiryEventAt oldVisit)
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit))
      (contributionCapacityRootTargetObstructionAuthority
        (capacityActionRootedAt oldVisit)) where
  compile := fun _ => contributionCapacityRequiresU8CompilationAt oldVisit

end
end M14SourceGeneratedContributionCapacityU8Revision
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Revision.generatedContributionCapacityTypedRevisionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Revision.generatedContributionCapacityU8CoreAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Revision.contributionCapacityCofaceRealizationCertificationAt
