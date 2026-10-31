import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source.SourceGeneratedM14RefusalCultureMaterial
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.SourceGeneratedM14InstitutionalCultureRepresentation

/-!
# Refusal-successor culture representation

The complete institutional culture representation is reindexed to the one
platform authority from which the paid successor departs.  Source and target
outer occurrences collide in that old face.  The independently grounded
refusal readout separates their actual successor currents and closes the
updated bidirectional kernel.

The revised quotient, unique factorizations, fixed-domain exhaustion, and
unique alternate-carrier equivalence are derived after exactness.  The source
seam lands in the post-settlement target root; this module does not identify
that root with the institutional U8 root's own generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Refusal
namespace Representation

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source

noncomputable section

def m14RefusalOldInstitutionalFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14RefusalOccurrenceAt oldVisit sourceIndex boundary →
      SourceGeneratedM14InstitutionalCultureFaceAt
        (m14InstitutionalBaseAt boundary) :=
  m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary ∘
    m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary

theorem m14RefusalOldInstitutionalKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14RefusalReindexedInstitutionalConsumersAt oldVisit sourceIndex
        boundary)
      (m14RefusalOldInstitutionalFaceReadAt oldVisit sourceIndex boundary) :=
  (m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary
    ).reindex
      (m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary)

@[simp] theorem m14RefusalOldInstitutionalFace_source_eq_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14RefusalOldInstitutionalFaceReadAt oldVisit sourceIndex boundary
        (m14RefusalSourceOccurrenceAt oldVisit sourceIndex boundary) =
      m14RefusalOldInstitutionalFaceReadAt oldVisit sourceIndex boundary
        (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary) :=
  congrArg
    (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary)
    (m14RefusalOldInstitutionalView_source_eq_target oldVisit sourceIndex
      boundary)

theorem m14RefusalCultureKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14RefusalOldInstitutionalFaceReadAt oldVisit sourceIndex boundary)
      (m14RefusalAuthorityReadoutAt oldVisit sourceIndex boundary) :=
  ⟨m14RefusalSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14RefusalOldInstitutionalFace_source_eq_target oldVisit sourceIndex
      boundary,
    m14Refusal_source_target_difference oldVisit sourceIndex boundary⟩

theorem m14RefusalCulture_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14RefusalAuthorityReadAt oldVisit sourceIndex boundary)
      (m14RefusalOldInstitutionalFaceReadAt oldVisit sourceIndex boundary) :=
  (m14RefusalCultureKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14RefusalCultureFaceRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right sameFace
  apply m14RefusalAuthorityRead_injective oldVisit sourceIndex boundary
  exact congrArg SourceGeneratedM14RefusalCultureFaceAt.refusalSuccessor
    sameFace

theorem m14RefusalCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary)
      (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right
  constructor
  · intro sameFace consumer
    cases consumer with
    | inl oldConsumer =>
        have sameOldFace := congrArg
          SourceGeneratedM14RefusalCultureFaceAt.institutionalCulture
          sameFace
        exact ((m14RefusalOldInstitutionalKernelExactAt oldVisit sourceIndex
          boundary) left right).1 sameOldFace oldConsumer
    | inr _unit =>
        exact congrArg SourceGeneratedM14RefusalCultureFaceAt.refusalSuccessor
          sameFace
  · intro sameConsumers
    have sameRefusal := sameConsumers (.inr PUnit.unit)
    have sameOccurrence := m14RefusalAuthorityRead_injective oldVisit
      sourceIndex boundary sameRefusal
    subst right
    rfl

noncomputable def m14RefusalCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary).Quotient ≃
      Set.range (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) :=
  (m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary
    ).quotientEquivRange

theorem m14RefusalCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer :
      (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary).Consumer) :
    ∃! factor :
        Set.range (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) →
          (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary
            ).Output consumer,
      ∀ occurrence,
        factor
            ⟨m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary).read
            consumer occurrence :=
  (m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization consumer

theorem m14Refusal_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) →
          M14RefusalAuthorityReadout,
      ∀ occurrence,
        factor
            ⟨m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          m14RefusalAuthorityReadAt oldVisit sourceIndex boundary
            occurrence :=
  (m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary
    ).newReadout_unique_factorization

theorem m14RefusalCultureEveryCurrentReadout_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Output : Type*}
    (readout : M14RefusalOccurrenceAt oldVisit sourceIndex boundary → Output) :
    ∃! factor :
        Set.range (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) →
          Output,
      ∀ occurrence,
        factor
            ⟨m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ = readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (m14RefusalCultureFaceRead_injective oldVisit sourceIndex boundary)
    readout

theorem m14RefusalCultureCompleteCarrier_uniqueIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Alternate : Type*}
    (alternate :
      M14RefusalOccurrenceAt oldVisit sourceIndex boundary → Alternate)
    (alternateExact : FaceKernelExactAt
      (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary)
      alternate) :
    ∃! equivalence :
        Set.range (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ := by
  let canonical := m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary
  refine ⟨canonical.completeCarrierEquiv alternateExact,
    canonical.completeCarrierEquiv_commutes alternateExact, ?_⟩
  intro candidate commutes
  exact canonical.completeCarrierEquiv_unique alternateExact candidate
    commutes

def m14RefusalCultureRefinedNormalFormAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  refinedFace
    (m14RefusalOldInstitutionalFaceReadAt oldVisit sourceIndex boundary)
    (m14RefusalAuthorityReadoutAt oldVisit sourceIndex boundary)

theorem m14RefusalCultureRefinedNormalForm_kernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary)
      (m14RefusalCultureRefinedNormalFormAt oldVisit sourceIndex boundary) :=
  (m14RefusalOldInstitutionalKernelExactAt oldVisit sourceIndex boundary
    ).adjoin_refinedFace

theorem m14RefusalCulture_sourceEquivNormalForm_uniqueAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range
            (m14RefusalCultureRefinedNormalFormAt oldVisit sourceIndex
              boundary),
      ∀ occurrence,
        equivalence
            ⟨m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨m14RefusalCultureRefinedNormalFormAt oldVisit sourceIndex boundary
              occurrence,
            occurrence, rfl⟩ :=
  m14RefusalCultureCompleteCarrier_uniqueIsoAt oldVisit sourceIndex boundary
    (m14RefusalCultureRefinedNormalFormAt oldVisit sourceIndex boundary)
    (m14RefusalCultureRefinedNormalForm_kernelExactAt oldVisit sourceIndex
      boundary)

theorem m14RefusalCultureRepresentation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    type_of% (sourceGeneratedM14RefusalCultureMaterial_directConsumer oldVisit
      sourceIndex boundary occurrence) ∧
      type_of% (m14RefusalCultureKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14RefusalCulture_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary) ∧
      Nonempty
        ((m14RefusalCultureConsumersAt oldVisit sourceIndex boundary
          ).Quotient ≃
          Set.range
            (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary)) ∧
      (∀ consumer,
        type_of% (m14RefusalCultureEveryConsumer_uniqueFactorizationAt
          oldVisit sourceIndex boundary consumer)) ∧
      type_of% (m14Refusal_updatedUniqueFactorizationAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14RefusalCulture_sourceEquivNormalForm_uniqueAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14RefusalNoPowerMinting_directConsumer oldVisit sourceIndex
        boundary) :=
  ⟨sourceGeneratedM14RefusalCultureMaterial_directConsumer oldVisit
      sourceIndex boundary occurrence,
    m14RefusalCultureKernelEscapeAt oldVisit sourceIndex boundary,
    m14RefusalCulture_oldFactorization_isEmpty oldVisit sourceIndex boundary,
    m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary,
    ⟨m14RefusalCultureQuotientEquivRangeAt oldVisit sourceIndex boundary⟩,
    m14RefusalCultureEveryConsumer_uniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14Refusal_updatedUniqueFactorizationAt oldVisit sourceIndex boundary,
    m14RefusalCulture_sourceEquivNormalForm_uniqueAt oldVisit sourceIndex
      boundary,
    m14RefusalNoPowerMinting_directConsumer oldVisit sourceIndex boundary⟩

end
end Representation
end Refusal
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation.m14RefusalCultureKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation.m14RefusalCultureKernelExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation.m14RefusalCultureQuotientEquivRangeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation.m14Refusal_updatedUniqueFactorizationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation.m14RefusalCultureCompleteCarrier_uniqueIsoAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation.m14RefusalCultureRepresentation_directConsumer
