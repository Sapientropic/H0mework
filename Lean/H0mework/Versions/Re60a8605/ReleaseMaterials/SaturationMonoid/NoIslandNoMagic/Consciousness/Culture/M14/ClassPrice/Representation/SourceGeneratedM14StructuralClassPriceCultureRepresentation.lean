import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source.SourceGeneratedM14StructuralClassPriceCultureMaterial

/-!
# Structural class-price culture representation

The complete refusal carrier is reindexed to the exact refusal target and is
therefore constant across the controller/affected dependent faces.  The class
and price consumers are defined independently of this carrier.  Their two
coordinates close the updated bidirectional kernel before quotient,
factorization, minimality or alternate-carrier equivalence is derived.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ClassPrice
namespace Representation

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source

noncomputable section

def m14StructuralClassPriceOldRefusalFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary →
      SourceGeneratedM14RefusalCultureFaceAt
        (m14InstitutionalBaseAt boundary) :=
  m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary ∘
    m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary

theorem m14StructuralClassPriceOldRefusalKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14StructuralClassPriceReindexedRefusalConsumersAt oldVisit sourceIndex
        boundary)
      (m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex
        boundary) :=
  (m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary).reindex
    (m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary)

@[simp] theorem m14StructuralClassPriceOldRefusalFace_source_eq_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex boundary
        (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
          boundary) =
      m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary) :=
  congrArg (m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary)
    (m14StructuralClassPriceOldRefusalView_source_eq_target oldVisit
      sourceIndex boundary)

theorem m14StructuralClassPriceCultureKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex
        boundary)
      (m14StructuralClassIndependentReadoutAt oldVisit sourceIndex boundary) :=
  ⟨m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14StructuralClassPriceOldRefusalFace_source_eq_target oldVisit sourceIndex
      boundary,
    (m14StructuralClassPriceRead_hasActualDifference oldVisit sourceIndex
      boundary).1⟩

theorem m14StructuralClassPriceCulture_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14StructuralClassReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex
        boundary) :=
  (m14StructuralClassPriceCultureKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14StructuralClassPriceCultureFaceRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
        boundary) := by
  intro left right sameFace
  apply m14StructuralClassRead_injective oldVisit sourceIndex boundary
  exact congrArg
    SourceGeneratedM14StructuralClassPriceCultureFaceAt.structuralClass
    sameFace

theorem m14StructuralClassPriceCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14StructuralClassPriceConsumersAt oldVisit sourceIndex boundary)
      (m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
        boundary) := by
  intro left right
  constructor
  · intro sameFace consumer
    cases consumer with
    | inl priorConsumer =>
        cases priorConsumer with
        | inl oldConsumer =>
            have sameOldFace := congrArg
              SourceGeneratedM14StructuralClassPriceCultureFaceAt.refusalCulture
              sameFace
            exact ((m14StructuralClassPriceOldRefusalKernelExactAt oldVisit
              sourceIndex boundary) left right).1 sameOldFace oldConsumer
        | inr _unit =>
            exact congrArg
              SourceGeneratedM14StructuralClassPriceCultureFaceAt.structuralClass
              sameFace
    | inr _unit =>
        exact congrArg
          SourceGeneratedM14StructuralClassPriceCultureFaceAt.structuralPrice
          sameFace
  · intro sameConsumers
    have sameClass := sameConsumers (.inl (.inr PUnit.unit))
    have sameOccurrence := m14StructuralClassRead_injective oldVisit
      sourceIndex boundary sameClass
    subst right
    rfl

noncomputable def m14StructuralClassPriceCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
      boundary).Quotient ≃
      Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
        boundary) :=
  (m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary
    ).quotientEquivRange

theorem m14StructuralClassPriceCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer :
      (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
        boundary).Consumer) :
    ∃! factor :
        Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) →
          (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
            boundary).Output consumer,
      ∀ occurrence,
        factor
            ⟨m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ =
          (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
            boundary).read consumer occurrence :=
  (m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization consumer

theorem m14StructuralClass_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) → M14StructuralActor,
      ∀ occurrence,
        factor
            ⟨m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ =
          m14StructuralClassReadAt occurrence :=
  (m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inl (.inr PUnit.unit))

theorem m14StructuralPrice_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) → M14StructuralPriceReadout,
      ∀ occurrence,
        factor
            ⟨m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ =
          m14StructuralPriceReadAt occurrence :=
  (m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inr PUnit.unit)

theorem m14StructuralClassPriceEveryCurrentReadout_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Output : Type*}
    (readout : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary → Output) :
    ∃! factor :
        Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) → Output,
      ∀ occurrence,
        factor
            ⟨m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ = readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (m14StructuralClassPriceCultureFaceRead_injective oldVisit sourceIndex
      boundary) readout

theorem m14StructuralClassPriceCompleteCarrier_uniqueIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Alternate : Type*}
    (alternate : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary → Alternate)
    (alternateExact : FaceKernelExactAt
      (m14StructuralClassPriceConsumersAt oldVisit sourceIndex boundary)
      alternate) :
    ∃! equivalence :
        Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) ≃ Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ := by
  let canonical := m14StructuralClassPriceCultureKernelExactAt oldVisit
    sourceIndex boundary
  refine ⟨canonical.completeCarrierEquiv alternateExact,
    canonical.completeCarrierEquiv_commutes alternateExact, ?_⟩
  intro candidate commutes
  exact canonical.completeCarrierEquiv_unique alternateExact candidate
    commutes

def m14StructuralClassPriceRefinedNormalFormAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  refinedFace
    (refinedFace
      (m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex
        boundary)
      (m14StructuralClassIndependentReadoutAt oldVisit sourceIndex boundary))
    (m14StructuralPriceIndependentReadoutAt oldVisit sourceIndex boundary)

theorem m14StructuralClassPriceRefinedNormalForm_kernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14StructuralClassPriceConsumersAt oldVisit sourceIndex boundary)
      (m14StructuralClassPriceRefinedNormalFormAt oldVisit sourceIndex
        boundary) :=
  (m14StructuralClassPriceOldRefusalKernelExactAt oldVisit sourceIndex
    boundary).adjoin_refinedFace.adjoin_refinedFace

theorem m14StructuralClassPrice_sourceEquivNormalForm_uniqueAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) ≃
          Set.range (m14StructuralClassPriceRefinedNormalFormAt oldVisit
            sourceIndex boundary),
      ∀ occurrence,
        equivalence
            ⟨m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ =
          ⟨m14StructuralClassPriceRefinedNormalFormAt oldVisit sourceIndex
              boundary occurrence,
            occurrence, rfl⟩ :=
  m14StructuralClassPriceCompleteCarrier_uniqueIsoAt oldVisit sourceIndex
    boundary
      (m14StructuralClassPriceRefinedNormalFormAt oldVisit sourceIndex
        boundary)
      (m14StructuralClassPriceRefinedNormalForm_kernelExactAt oldVisit
        sourceIndex boundary)

theorem m14StructuralClassPriceCultureRepresentation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    type_of%
        (sourceGeneratedM14StructuralClassPriceCultureMaterial_directConsumer
          oldVisit sourceIndex boundary occurrence) ∧
      type_of% (m14StructuralClassPriceCultureKernelEscapeAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCulture_oldFactorization_isEmpty
        oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCultureKernelExactAt oldVisit
        sourceIndex boundary) ∧
      Nonempty
        ((m14StructuralClassPriceConsumersAt oldVisit sourceIndex
          boundary).Quotient ≃
          Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
            sourceIndex boundary)) ∧
      (∀ consumer,
        type_of%
          (m14StructuralClassPriceCultureEveryConsumer_uniqueFactorizationAt
            oldVisit sourceIndex boundary consumer)) ∧
      type_of% (m14StructuralClass_updatedUniqueFactorizationAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralPrice_updatedUniqueFactorizationAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPrice_sourceEquivNormalForm_uniqueAt
        oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceNoForgery_directConsumer oldVisit
        sourceIndex boundary) :=
  ⟨sourceGeneratedM14StructuralClassPriceCultureMaterial_directConsumer
      oldVisit sourceIndex boundary occurrence,
    m14StructuralClassPriceCultureKernelEscapeAt oldVisit sourceIndex
      boundary,
    m14StructuralClassPriceCulture_oldFactorization_isEmpty oldVisit
      sourceIndex boundary,
    m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary,
    ⟨m14StructuralClassPriceCultureQuotientEquivRangeAt oldVisit sourceIndex
      boundary⟩,
    m14StructuralClassPriceCultureEveryConsumer_uniqueFactorizationAt oldVisit
      sourceIndex boundary,
    m14StructuralClass_updatedUniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14StructuralPrice_updatedUniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14StructuralClassPrice_sourceEquivNormalForm_uniqueAt oldVisit sourceIndex
      boundary,
    m14StructuralClassPriceNoForgery_directConsumer oldVisit sourceIndex
      boundary⟩

end
end Representation
end ClassPrice
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.m14StructuralClassPriceCultureKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.m14StructuralClassPriceCultureKernelExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.m14StructuralClassPriceCultureQuotientEquivRangeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.m14StructuralClass_updatedUniqueFactorizationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.m14StructuralClassPriceCompleteCarrier_uniqueIsoAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.m14StructuralClassPriceCultureRepresentation_directConsumer
