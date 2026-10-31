import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Revision.Root.SourceGeneratedContributionCapacityRepresentationPairIntentU8Root

/-!
# Pair-intent source-generated U8 revision

The installed pair-intent failure generates its canonical minimal coface, a
field-grounded typed revision, and a U8 revision core.  All revised fields are
definitionally grounded in the same coface.  The canonical first write has one
successor and moves the revised root from ingress `false` to active `true`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root

def representationIntentGeneratedTypedRevision
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    GeneratedTypedSemanticWorldNetworkRevisionAt
      (RepresentationIntentRootedAt oldVisit sourceIndex boundary) where
  NewN := RepresentationIntentU8NAt oldVisit sourceIndex boundary
  translation :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary).translation
  NewV := RepresentationIntentU8VAt oldVisit sourceIndex boundary
  newLivingRoot :=
    representationIntentU8LivingRoot oldVisit sourceIndex boundary
  new_support_restricts :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).firstWrite_targetSupport_is_cofaceRestriction
  oldTargetOpenLedger :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).cofaceLedgerRetract
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation :=
    representationIntentU8OccurrencePresentation oldVisit sourceIndex boundary
  occurrence_commutes := rfl
  firstWrite :=
    representationIntentU8FirstWrite oldVisit sourceIndex boundary
  newOnlyEntry :=
    representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary
  newOnlyProgressBudget_eq_zero := rfl
  revisedClaimHolds :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).obstructionClaimHolds
  semanticChange :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).obstructionSemanticChange
  revisedClaim_hasNoOldPreimage :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).obstructionClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).obstructionIncidence_hasNoOldPreimage
  oldEntryRows :=
    representationIntentU8OldEntryRows oldVisit sourceIndex boundary
  newOnlyEntry_hasNoOldPreimage :=
    (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).obstructionEntry_hasNoOldPreimage
  newOnlyEntryRow :=
    representationIntentU8GeneratedRow oldVisit sourceIndex boundary

def representationIntentU8FirstSuccessor
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      (representationIntentGeneratedTypedRevision oldVisit sourceIndex boundary
        ).initialRestructuringGenerated.occurrence
      (representationIntentGeneratedTypedRevision oldVisit sourceIndex boundary
        ).initialRestructuringGenerated.wholeLedgerWriteBack :=
  PUnit.unit

theorem representationIntentU8FirstSuccessor_unique
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (candidate :
      SourceNativeLedgerGeneratedSuccessorAt
        (representationIntentGeneratedTypedRevision oldVisit sourceIndex
          boundary).initialRestructuringGenerated.occurrence
        (representationIntentGeneratedTypedRevision oldVisit sourceIndex
          boundary).initialRestructuringGenerated.wholeLedgerWriteBack) :
    candidate =
      representationIntentU8FirstSuccessor oldVisit sourceIndex boundary := by
  change candidate = (PUnit.unit : PUnit)
  cases candidate
  rfl

@[simp] theorem representationIntentU8FirstSuccessor_targetCurrent_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8FirstSuccessor oldVisit sourceIndex boundary
      ).targetCurrent = true :=
  rfl

theorem representationIntentGeneratedTypedRevision_exactGrounding
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentGeneratedTypedRevision oldVisit sourceIndex boundary
      ).ExactFieldGrounding where
  network_eq := rfl
  lawSurface_heq := HEq.rfl
  translation_heq := HEq.rfl
  initialSupport_heq := HEq.rfl
  oldTargetOpenLedger_heq := HEq.rfl
  newOnlyEntry_heq := HEq.rfl
  revisedClaimHolds_heq := HEq.rfl
  semanticChange_heq := HEq.rfl

def representationIntentFieldGroundedRevision
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt
      (RepresentationIntentRootedAt oldVisit sourceIndex boundary) :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofGeneratedOccurrence
    (representationIntentGeneratedTypedRevision oldVisit sourceIndex boundary)
    (representationIntentGeneratedTypedRevision_exactGrounding oldVisit
      sourceIndex boundary)

def representationIntentFailureInquiryEvent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  ULift.up.{1, 0}
    ((InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
      ).emitted
        (InstalledRepresentationIntentVisitAt oldVisit sourceIndex
          boundary).current)

def representationIntentFailureFrontier
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceFrontierAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
      (representationIntentU7At oldVisit sourceIndex boundary)
      (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary)
      (representationPairIntentTheoryAt oldVisit sourceIndex boundary) ()
      (representationIntentFailureInquiryEvent oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
        ).target.targetAuthority
      (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
      (representationIntentU7GateAt oldVisit sourceIndex boundary)
      (representationPairIntentFailureAt oldVisit sourceIndex boundary) :=
  SourceNativeInquiryCofaceFrontierAt.ofRootFailureFace
    (installedRepresentationFailureFaceAt oldVisit sourceIndex boundary)
    rfl (representationIntentFailureSuccessorAt oldVisit sourceIndex boundary)

@[simp] theorem representationIntentFailureFrontier_rooted_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentFailureFrontier oldVisit sourceIndex boundary).rooted =
      RepresentationIntentRootedAt oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem representationIntentFailureFrontier_coface_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentFailureFrontier oldVisit sourceIndex boundary).coface =
      RepresentationIntentCofaceAt oldVisit sourceIndex boundary :=
  rfl

def representationIntentCofaceRealizationCandidate
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationAt
      (representationIntentFailureFrontier oldVisit sourceIndex boundary) :=
  SourceNativeInquiryCofaceRealizationAt.ofGeneratedRevision
    (representationIntentGeneratedTypedRevision oldVisit sourceIndex boundary)

def representationIntentGeneratedU8Core
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedInquiryU8RevisionCoreAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
      (representationIntentU7At oldVisit sourceIndex boundary)
      (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary)
      (representationPairIntentTheoryAt oldVisit sourceIndex boundary) ()
      (representationIntentFailureInquiryEvent oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
        ).target.targetAuthority
      (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
      (representationIntentU7GateAt oldVisit sourceIndex boundary)
      (representationPairIntentFailureAt oldVisit sourceIndex boundary) where
  frontier := representationIntentFailureFrontier oldVisit sourceIndex boundary
  revision :=
    representationIntentFieldGroundedRevision oldVisit sourceIndex boundary

theorem representationIntentCofaceRealizationCertification
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryCofaceRealizationCertificationAt
      (representationIntentCofaceRealizationCandidate oldVisit sourceIndex
        boundary)
      (representationIntentGeneratedU8Core oldVisit sourceIndex boundary) where
  frontier_eq := rfl
  source_heq := HEq.rfl

def representationIntentGeneratedU8Core_cofaceFactorization
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentGeneratedU8Core oldVisit sourceIndex boundary
    ).cofaceFactorization

theorem representationIntentU8Revision_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentGeneratedTypedRevision oldVisit sourceIndex boundary
      ).NewN =
        (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
          ).worldNetwork ∧
      (representationIntentU8LivingRoot oldVisit sourceIndex boundary
        ).source.base.lawSurface =
        TheoryState.rootSemantic
          (RepresentationIntentU8NAt oldVisit sourceIndex boundary) ∧
      (∀ entry :
        (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry,
        representationIntentU8EntryAt oldVisit sourceIndex boundary
            (representationIntentU8EntryIndex oldVisit sourceIndex boundary
              entry) = entry) ∧
      (representationIntentGeneratedTypedRevision oldVisit sourceIndex boundary
        ).newOnlyEntry =
        (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
          ).obstructionEntry ∧
      (representationIntentU8FirstSuccessor oldVisit sourceIndex boundary
        ).targetCurrent = true ∧
      Nonempty
        (SourceGeneratedInquiryU8RevisionCoreAt
          (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
          (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
          (representationIntentU7At oldVisit sourceIndex boundary)
          (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex
            boundary)
          (representationPairIntentTheoryAt oldVisit sourceIndex boundary) ()
          (representationIntentFailureInquiryEvent oldVisit sourceIndex
            boundary)
          (representationResidualBearerAt oldVisit sourceIndex boundary)
          (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
            ).target.targetAuthority
          (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
          (representationIntentU7GateAt oldVisit sourceIndex boundary)
          (representationPairIntentFailureAt oldVisit sourceIndex boundary)) :=
  ⟨rfl, rfl,
    representationIntentU8EntryAt_index oldVisit sourceIndex boundary,
    rfl, rfl, ⟨representationIntentGeneratedU8Core oldVisit sourceIndex
      boundary⟩⟩

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision.representationIntentGeneratedTypedRevision
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision.representationIntentFieldGroundedRevision
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision.representationIntentU8FirstSuccessor_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision.representationIntentGeneratedU8Core
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision.representationIntentGeneratedU8Core_cofaceFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision.representationIntentU8Revision_directConsumer
