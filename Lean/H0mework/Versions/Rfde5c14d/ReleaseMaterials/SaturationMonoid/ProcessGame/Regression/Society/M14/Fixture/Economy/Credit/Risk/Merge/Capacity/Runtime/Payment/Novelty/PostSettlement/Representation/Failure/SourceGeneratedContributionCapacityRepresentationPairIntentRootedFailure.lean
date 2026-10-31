import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Action.SourceGeneratedSequentialContributionCapacityRepresentationPairIntent

/-!
# Same-visit rooted representation failure

The generated sequential action has already installed the pair-intent root
and reached its active Bool visit.  This file recognizes three coordinates of
that exact occurrence: the intent payload carrying semantic change, the
requires-U8 inquiry payload, and the canonical failure token.  The existing
target-obstruction row supplies authoritative bearer continuity; its claim is
not identified with the new obstruction claim.

The rooted failure uses the target root's ordinary nonterminal continuation.
The failure token does not mint a successor.  The minimal coface is then the
existing kernel producer which creates the new claim-bearing row.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
open M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent

abbrev InstalledRepresentationIntentActionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  generatedRepresentationIntentActionAt oldVisit sourceIndex boundary

abbrev InstalledRepresentationIntentRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
    ).target.targetRoot

abbrev InstalledRepresentationIntentVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
    ).target.targetVisit

def installedRepresentationIntentFaceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRootSemanticFaceAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary) where
  projection := .inherited RepresentationIntentProjection.intent
  active := representationIntentIntentActiveAt oldVisit sourceIndex boundary
  classifier_eq :=
    representationIntentClassifier_intent_true oldVisit sourceIndex boundary

theorem installedRepresentationIntentFace_rootRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (installedRepresentationIntentFaceAt oldVisit sourceIndex boundary
        ).rootRead
      (sourceGeneratedRepresentationIntentPayloadAt oldVisit sourceIndex
        boundary) :=
  HEq.rfl

def installedRepresentationInquiryFaceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRootSemanticFaceAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary) where
  projection := .inherited RepresentationIntentProjection.inquiry
  active := representationIntentInquiryActiveAt oldVisit sourceIndex boundary
  classifier_eq :=
    representationIntentClassifier_inquiry_true oldVisit sourceIndex boundary

theorem installedRepresentationInquiryFace_rootRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (installedRepresentationInquiryFaceAt oldVisit sourceIndex boundary
        ).rootRead
      ((representationIntentProjectionLawAt oldVisit sourceIndex boundary
        ).project .inquiry
          (representationIntentEmitted oldVisit sourceIndex boundary true)
          (representationIntentInquiryActiveAt oldVisit sourceIndex
            boundary)) :=
  HEq.rfl

theorem representationIntentFailureRootDispositionCommutesAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    U7DemandEntryRootDispositionCommutesAt
      (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary)
      (representationIntentU7EventAt oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary)
      (((InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
          ((InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
            ).emitted
              (InstalledRepresentationIntentVisitAt oldVisit sourceIndex
                boundary).current)).entryDisposition
        (representationResidualBearerAt oldVisit sourceIndex boundary)) :=
  ⟨HEq.rfl, HEq.rfl⟩

def installedRepresentationFailureFaceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRootExpressibilityFailureFaceAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
      (U7 := representationIntentU7At oldVisit sourceIndex boundary)
      (representationPairIntentFailureAt oldVisit sourceIndex boundary) where
  lawSurface_eq := rfl
  projection := .inherited RepresentationIntentProjection.failure
  active := representationIntentFailureActiveAt oldVisit sourceIndex boundary
  classifier_eq :=
    representationIntentClassifier_failure_true oldVisit sourceIndex boundary
  calculus :=
    representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary
  u7Event := representationIntentU7EventAt oldVisit sourceIndex boundary
  u7Event_eq_emit := rfl
  theoryAudit := representationIntentU7GateAt oldVisit sourceIndex boundary
  support_eq := rfl
  rootEntry := representationResidualBearerAt oldVisit sourceIndex boundary
  rootEntryAtFailure_eq := rfl
  rootDispositionCommutes :=
    representationIntentFailureRootDispositionCommutesAt oldVisit sourceIndex
      boundary
  project_heq := HEq.rfl

def representationIntentFailureSuccessorAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    CausalEntrySuccessorAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary) :=
  CausalEntrySuccessorAt.ofNonterminal rfl

def representationIntentRootedFailureAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RootedActualExpressibilityFailureAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
      (representationIntentU7At oldVisit sourceIndex boundary)
      (representationPairIntentFailureAt oldVisit sourceIndex boundary) :=
  RootedActualExpressibilityFailureAt.ofRootFailureFace
    (installedRepresentationFailureFaceAt oldVisit sourceIndex boundary)
    (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
      ).target.targetAuthority.toAuthoritativeAuthority
    (representationIntentFailureSuccessorAt oldVisit sourceIndex boundary)

def representationIntentGeneratedMinimalCofaceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    GeneratedMinimalCofaceAt
      (representationIntentRootedFailureAt oldVisit sourceIndex boundary) :=
  root_obstruction_generates_minimal_coface
    (representationIntentRootedFailureAt oldVisit sourceIndex boundary)

@[simp] theorem representationIntentRootedFailure_entry_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentRootedFailureAt oldVisit sourceIndex boundary
      ).rootEntry =
      representationResidualBearerAt oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem representationIntentRootedFailure_visit_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary
      ).current = true :=
  rfl

theorem representationIntentRootedFailure_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RepresentationIntentActionReceiptCoreAt oldVisit sourceIndex boundary
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary) ∧
      type_of% (installedRepresentationIntentFace_rootRead_exact oldVisit
        sourceIndex boundary) ∧
      type_of% (installedRepresentationInquiryFace_rootRead_exact oldVisit
        sourceIndex boundary) ∧
      type_of%
        (installedRepresentationFailureFaceAt oldVisit sourceIndex boundary
          ).installedAuthority_factorizes ∧
      (representationIntentRootedFailureAt oldVisit sourceIndex boundary
        ).rootEntry =
        representationResidualBearerAt oldVisit sourceIndex boundary ∧
      HEq
        (representationIntentRootedFailureAt oldVisit sourceIndex boundary
          ).authority
        (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
          ).target.targetAuthority.toAuthoritativeAuthority ∧
      (representationIntentRootedFailureAt oldVisit sourceIndex boundary
        ).successor =
        representationIntentFailureSuccessorAt oldVisit sourceIndex boundary ∧
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary
        ).current = true ∧
      (representationResidualBearerAt oldVisit sourceIndex boundary).claim ≠
        (RepresentationIntentNAt oldVisit sourceIndex boundary).obstructionClaim
          (generatedRepresentationObstructionAt oldVisit sourceIndex boundary) ∧
      (representationIntentGeneratedMinimalCofaceAt oldVisit sourceIndex
        boundary).obstructionEntry.claim =
        (representationIntentGeneratedMinimalCofaceAt oldVisit sourceIndex
          boundary).obstructionClaim ∧
      Nonempty
        ((RepresentationIntentNAt oldVisit sourceIndex boundary).SemanticChangeAt
          (representationIntentSupportAt oldVisit sourceIndex boundary)
          (representationResidualBearerAt oldVisit sourceIndex boundary).claim
          (generatedRepresentationClaimAt oldVisit sourceIndex boundary)) :=
  ⟨generatedRepresentationIntentAction_receiptCore_exact oldVisit sourceIndex
      boundary,
    installedRepresentationIntentFace_rootRead_exact oldVisit sourceIndex
      boundary,
    installedRepresentationInquiryFace_rootRead_exact oldVisit sourceIndex
      boundary,
    (installedRepresentationFailureFaceAt oldVisit sourceIndex boundary
      ).installedAuthority_factorizes,
    rfl, HEq.rfl, rfl, rfl,
    representationResidualBearer_claim_ne_obstructionClaim oldVisit sourceIndex
      boundary,
    (representationIntentGeneratedMinimalCofaceAt oldVisit sourceIndex boundary
      ).obstructionEntry_claim_eq_obstructionClaim,
    ⟨sourceGeneratedRepresentationSemanticChangeAt oldVisit sourceIndex
      boundary⟩⟩

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure.installedRepresentationIntentFaceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure.installedRepresentationInquiryFace_rootRead_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure.installedRepresentationFailureFaceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure.representationIntentRootedFailureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure.representationIntentGeneratedMinimalCofaceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure.representationIntentRootedFailure_directConsumer
