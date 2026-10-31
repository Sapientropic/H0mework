import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source.SourceGeneratedM14InstitutionalCultureMaterial
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation.SourceGeneratedM14CultureRepresentation

/-!
# Actual-U8 institutional revision of the M14 culture representation

The old culture system is restricted along the source-owned forgetting map
from the generated revised-channel domain to its one relation-side culture
occurrence.  The independent institutional-authority consumer escapes that
old kernel.  The complete source face then joins the old culture history to
the new authority/material readout and proves the exact updated kernel.

Only after the bidirectional theorem do we derive the revised quotient,
unique factorizations, fixed-domain exhaustion, and unique commuting
equivalence with every alternate complete carrier.  The generic refined-face
normal form is compared to the source material by the same exact kernel; it
does not mint the paid U8 authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Institution
namespace Representation

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source

noncomputable section

def m14InstitutionalOldCultureFaceReadAt (boundary : Nat) :
    M14InstitutionalChannelOccurrenceAt boundary →
      SourceGeneratedM14CultureFaceAt (m14InstitutionalBaseAt boundary) :=
  m14CultureFaceReadAt (m14InstitutionalBaseAt boundary) ∘
    m14InstitutionalOldCultureViewAt boundary

theorem m14InstitutionalOldCultureKernelExactAt (boundary : Nat) :
    FaceKernelExactAt (m14InstitutionalReindexedCultureConsumersAt boundary)
      (m14InstitutionalOldCultureFaceReadAt boundary) :=
  (m14CultureKernelExactAt (m14InstitutionalBaseAt boundary)).reindex
    (m14InstitutionalOldCultureViewAt boundary)

theorem m14InstitutionalOldCultureFace_tenure_eq_platform
    (boundary : Nat) :
    m14InstitutionalOldCultureFaceReadAt boundary
        (m14InstitutionalTenureOccurrenceAt boundary) =
      m14InstitutionalOldCultureFaceReadAt boundary
        (m14InstitutionalPlatformOccurrenceAt boundary) :=
  rfl

/-- The actual institutional consumer escapes the complete old culture face,
not merely a name or current-practice projection. -/
theorem m14InstitutionalCultureKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt (m14InstitutionalOldCultureFaceReadAt boundary)
      (m14InstitutionalAuthorityReadoutAt oldVisit sourceIndex boundary) :=
  ⟨m14InstitutionalTenureOccurrenceAt boundary,
    m14InstitutionalPlatformOccurrenceAt boundary,
    m14InstitutionalOldCultureFace_tenure_eq_platform boundary,
    m14InstitutionalAuthority_tenure_ne_platform oldVisit sourceIndex
      boundary⟩

theorem m14InstitutionalCulture_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14InstitutionalAuthorityReadAt oldVisit sourceIndex boundary)
      (m14InstitutionalOldCultureFaceReadAt boundary) :=
  (m14InstitutionalCultureKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14InstitutionalCultureFaceRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right sameFace
  apply m14InstitutionalAuthorityRead_injective oldVisit sourceIndex boundary
  exact congrArg
    SourceGeneratedM14InstitutionalCultureFaceAt.institutionalAuthority
    sameFace

/-- Updated bidirectional kernel exactness. -/
theorem m14InstitutionalCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary)
      (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right
  constructor
  · intro sameFace consumer
    cases consumer with
    | inl oldConsumer =>
        have sameOldFace := congrArg
          SourceGeneratedM14InstitutionalCultureFaceAt.cultureHistory
          sameFace
        exact ((m14InstitutionalOldCultureKernelExactAt boundary) left right
          ).1 sameOldFace oldConsumer
    | inr _unit =>
        exact congrArg
          SourceGeneratedM14InstitutionalCultureFaceAt.institutionalAuthority
          sameFace
  · intro sameConsumers
    have sameAuthority := sameConsumers (.inr PUnit.unit)
    have sameOccurrence :=
      m14InstitutionalAuthorityRead_injective oldVisit sourceIndex boundary
        sameAuthority
    subst right
    rfl

noncomputable def m14InstitutionalCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
      ).Quotient ≃
      Set.range
        (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) :=
  (m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary
    ).quotientEquivRange

theorem m14InstitutionalCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer :
      (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
        ).Consumer) :
    ∃! factor :
        Set.range
            (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) →
          (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
            ).Output consumer,
      ∀ occurrence,
        factor
            ⟨m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
            ).read consumer occurrence :=
  (m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization consumer

theorem m14InstitutionalAuthority_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range
            (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) →
          M14InstitutionalAuthorityReadout,
      ∀ occurrence,
        factor
            ⟨m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          m14InstitutionalAuthorityReadAt oldVisit sourceIndex boundary
            occurrence :=
  (m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary
    ).newReadout_unique_factorization

theorem m14InstitutionalCultureEveryCurrentReadout_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Output : Type*}
    (readout : M14InstitutionalChannelOccurrenceAt boundary → Output) :
    ∃! factor :
        Set.range
            (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) →
          Output,
      ∀ occurrence,
        factor
            ⟨m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ = readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (m14InstitutionalCultureFaceRead_injective oldVisit sourceIndex boundary)
    readout

theorem m14InstitutionalCultureCompleteCarrier_uniqueIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Alternate : Type*}
    (alternate : M14InstitutionalChannelOccurrenceAt boundary → Alternate)
    (alternateExact : FaceKernelExactAt
      (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary)
      alternate) :
    ∃! equivalence :
        Set.range
            (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ := by
  let canonical :=
    m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary
  refine ⟨canonical.completeCarrierEquiv alternateExact,
    canonical.completeCarrierEquiv_commutes alternateExact, ?_⟩
  intro candidate commutes
  exact canonical.completeCarrierEquiv_unique
    alternateExact candidate commutes

/-- The generic G8 normal form has the same exact kernel as the source face,
so there is one commuting equivalence on the generated channel occurrences. -/
def m14InstitutionalCultureRefinedNormalFormAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  refinedFace (m14InstitutionalOldCultureFaceReadAt boundary)
    (m14InstitutionalAuthorityReadoutAt oldVisit sourceIndex boundary)

theorem m14InstitutionalCultureRefinedNormalForm_kernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary)
      (m14InstitutionalCultureRefinedNormalFormAt oldVisit sourceIndex
        boundary) :=
  (m14InstitutionalOldCultureKernelExactAt boundary).adjoin_refinedFace

theorem m14InstitutionalCulture_sourceEquivNormalForm_uniqueAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range
            (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range
            (m14InstitutionalCultureRefinedNormalFormAt oldVisit sourceIndex
              boundary),
      ∀ occurrence,
        equivalence
            ⟨m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨m14InstitutionalCultureRefinedNormalFormAt oldVisit sourceIndex
              boundary occurrence,
            occurrence, rfl⟩ :=
  m14InstitutionalCultureCompleteCarrier_uniqueIsoAt oldVisit sourceIndex
    boundary
    (m14InstitutionalCultureRefinedNormalFormAt oldVisit sourceIndex boundary)
    (m14InstitutionalCultureRefinedNormalForm_kernelExactAt oldVisit
      sourceIndex boundary)

theorem m14InstitutionalCultureRepresentation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14InstitutionalChannelOccurrenceAt boundary) :
    type_of% (sourceGeneratedM14InstitutionalCultureMaterial_directConsumer
      oldVisit sourceIndex boundary occurrence) ∧
      type_of% (m14InstitutionalCultureKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14InstitutionalCulture_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14InstitutionalCultureKernelExactAt oldVisit sourceIndex
        boundary) ∧
      Nonempty
        ((m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
          ).Quotient ≃
          Set.range
            (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary)) ∧
      (∀ consumer,
        type_of% (m14InstitutionalCultureEveryConsumer_uniqueFactorizationAt
          oldVisit sourceIndex boundary consumer)) ∧
      type_of% (m14InstitutionalAuthority_updatedUniqueFactorizationAt
        oldVisit sourceIndex boundary) ∧
      type_of% (m14InstitutionalCulture_sourceEquivNormalForm_uniqueAt
        oldVisit sourceIndex boundary) :=
  ⟨sourceGeneratedM14InstitutionalCultureMaterial_directConsumer oldVisit
      sourceIndex boundary occurrence,
    m14InstitutionalCultureKernelEscapeAt oldVisit sourceIndex boundary,
    m14InstitutionalCulture_oldFactorization_isEmpty oldVisit sourceIndex
      boundary,
    m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary,
    ⟨m14InstitutionalCultureQuotientEquivRangeAt oldVisit sourceIndex
      boundary⟩,
    m14InstitutionalCultureEveryConsumer_uniqueFactorizationAt oldVisit
      sourceIndex boundary,
    m14InstitutionalAuthority_updatedUniqueFactorizationAt oldVisit
      sourceIndex boundary,
    m14InstitutionalCulture_sourceEquivNormalForm_uniqueAt oldVisit
      sourceIndex boundary⟩

end
end Representation
end Institution
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.m14InstitutionalCultureKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.m14InstitutionalCultureKernelExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.m14InstitutionalCultureQuotientEquivRangeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.m14InstitutionalAuthority_updatedUniqueFactorizationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.m14InstitutionalCultureCompleteCarrier_uniqueIsoAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.m14InstitutionalCulture_sourceEquivNormalForm_uniqueAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.m14InstitutionalCultureRepresentation_directConsumer
