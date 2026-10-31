import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer.IndependentM14ArtProductionConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.SourceGeneratedM14TeachingCultureRepresentation

/-!
# Source-generated M14 art-production culture representation

The complete teaching culture face is constant on the raw/produced work
restrictions of one actual progress receipt.  Independently declared work and
lifecycle/write-back consumers separate them.  The source-generated combined
face closes the exact kernel before quotient, factorization or unique-iso
results are derived.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ArtProduction
namespace Representation

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer

noncomputable section

structure SourceGeneratedM14ArtProductionCultureFaceAt (base : Nat) : Type where
  teachingCulture : SourceGeneratedM14TeachingCultureFaceAt base
  producedWork : M14ArtWorkReadout
  productionLifecycle : M14ArtProductionLifecycleReadout

def m14ArtProductionOldTeachingFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
      SourceGeneratedM14TeachingCultureFaceAt
        (m14InstitutionalBaseAt boundary) :=
  m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary ∘
    m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary

def m14ArtProductionCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14ArtProductionCultureFaceAt
      (m14InstitutionalBaseAt boundary) where
  teachingCulture := m14ArtProductionOldTeachingFaceReadAt oldVisit
    sourceIndex boundary occurrence
  producedWork := m14ArtProductionWorkReadAt occurrence
  productionLifecycle := m14ArtProductionLifecycleReadAt occurrence

inductive SourceGeneratedM14ArtProductionCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type
  | private generated

def generateM14ArtProductionCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14ArtProductionCultureFaceTokenAt oldVisit sourceIndex
      boundary :=
  .generated

namespace SourceGeneratedM14ArtProductionCultureFaceTokenAt

def read
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_token : SourceGeneratedM14ArtProductionCultureFaceTokenAt oldVisit
      sourceIndex boundary)
    (occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14ArtProductionCultureFaceAt
      (m14InstitutionalBaseAt boundary) :=
  m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary occurrence

end SourceGeneratedM14ArtProductionCultureFaceTokenAt

structure SourceGeneratedM14ArtProductionCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  face : SourceGeneratedM14ArtProductionCultureFaceTokenAt oldVisit sourceIndex
    boundary
  faceExact : face = generateM14ArtProductionCultureFaceTokenAt oldVisit
    sourceIndex boundary
      (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary)
  teachingMaterial : SourceGeneratedM14TeachingCultureMaterialAt oldVisit
    sourceIndex boundary
  teachingMaterialExact : teachingMaterial =
    sourceGeneratedM14TeachingCultureMaterialAt oldVisit sourceIndex boundary
      (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary)
  artSource : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
    boundary
  artSourceExact : artSource =
    sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary

def sourceGeneratedM14ArtProductionCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14ArtProductionCultureMaterialAt oldVisit sourceIndex
      boundary where
  face := generateM14ArtProductionCultureFaceTokenAt oldVisit sourceIndex
    boundary occurrence
  faceExact := rfl
  teachingMaterial := sourceGeneratedM14TeachingCultureMaterialAt oldVisit
    sourceIndex boundary
      (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary)
  teachingMaterialExact := rfl
  artSource := sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
    boundary
  artSourceExact := rfl

@[simp] theorem m14ArtProductionCultureMaterial_faceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    (sourceGeneratedM14ArtProductionCultureMaterialAt oldVisit sourceIndex
      boundary occurrence).face.read occurrence =
      m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
        occurrence :=
  rfl

theorem sourceGeneratedM14ArtProductionCultureMaterial_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    let material := sourceGeneratedM14ArtProductionCultureMaterialAt oldVisit
      sourceIndex boundary occurrence
    Nonempty (SourceGeneratedM14ArtProductionCultureMaterialAt oldVisit
        sourceIndex boundary) ∧
      material.face.read occurrence =
        m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
          occurrence ∧
      material.teachingMaterial =
        sourceGeneratedM14TeachingCultureMaterialAt oldVisit sourceIndex
          boundary
            (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary) ∧
      material.artSource =
        sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary ∧
      type_of% (sourceGeneratedM14ActualArtProduction_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProductionConsumer_grounded oldVisit sourceIndex
        boundary) := by
  let material := sourceGeneratedM14ArtProductionCultureMaterialAt oldVisit
    sourceIndex boundary occurrence
  exact ⟨⟨material⟩, rfl, material.teachingMaterialExact,
    material.artSourceExact,
    sourceGeneratedM14ActualArtProduction_directConsumer oldVisit sourceIndex
      boundary,
    m14ArtProductionConsumer_grounded oldVisit sourceIndex boundary⟩

theorem m14ArtProductionOldTeachingKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14ArtProductionReindexedTeachingConsumersAt oldVisit sourceIndex
        boundary)
      (m14ArtProductionOldTeachingFaceReadAt oldVisit sourceIndex boundary) :=
  (m14TeachingCultureKernelExactAt oldVisit sourceIndex boundary).reindex
    (m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary)

@[simp] theorem m14ArtProductionOldTeachingFace_raw_eq_work
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14ArtProductionOldTeachingFaceReadAt oldVisit sourceIndex boundary
        (m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary) =
      m14ArtProductionOldTeachingFaceReadAt oldVisit sourceIndex boundary
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary) :=
  congrArg (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary)
    (m14ArtProductionOldTeachingView_raw_eq_work oldVisit sourceIndex boundary)

theorem m14ArtProductionCultureKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14ArtProductionOldTeachingFaceReadAt oldVisit sourceIndex boundary)
      (m14ArtProductionWorkIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary,
    m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary,
    m14ArtProductionOldTeachingFace_raw_eq_work oldVisit sourceIndex boundary,
    m14ArtProductionWorkRead_raw_ne_work oldVisit sourceIndex boundary⟩

theorem m14ArtProductionCulture_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14ArtProductionWorkReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14ArtProductionOldTeachingFaceReadAt oldVisit sourceIndex boundary) :=
  (m14ArtProductionCultureKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14ArtProductionCultureFaceRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right sameFace
  apply m14ArtProductionWorkRead_injective oldVisit sourceIndex boundary
  exact congrArg
    SourceGeneratedM14ArtProductionCultureFaceAt.producedWork sameFace

theorem m14ArtProductionCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14ArtProductionConsumersAt oldVisit sourceIndex boundary)
      (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right
  constructor
  · intro sameFace consumer
    cases consumer with
    | inl priorConsumer =>
        cases priorConsumer with
        | inl oldConsumer =>
            have sameOldFace := congrArg
              SourceGeneratedM14ArtProductionCultureFaceAt.teachingCulture
              sameFace
            exact ((m14ArtProductionOldTeachingKernelExactAt oldVisit
              sourceIndex boundary) left right).1 sameOldFace oldConsumer
        | inr _unit =>
            exact congrArg
              SourceGeneratedM14ArtProductionCultureFaceAt.producedWork
              sameFace
    | inr _unit =>
        exact congrArg
          SourceGeneratedM14ArtProductionCultureFaceAt.productionLifecycle
          sameFace
  · intro sameConsumers
    have sameWork := sameConsumers (.inl (.inr PUnit.unit))
    have sameOccurrence := m14ArtProductionWorkRead_injective oldVisit
      sourceIndex boundary sameWork
    subst right
    rfl

noncomputable def m14ArtProductionCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionConsumersAt oldVisit sourceIndex boundary).Quotient ≃
      Set.range
        (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary) :=
  (m14ArtProductionCultureKernelExactAt oldVisit sourceIndex boundary
    ).quotientEquivRange

theorem m14ArtProductionCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer : (m14ArtProductionConsumersAt oldVisit sourceIndex
      boundary).Consumer) :
    ∃! factor :
        Set.range (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex
          boundary) →
          (m14ArtProductionConsumersAt oldVisit sourceIndex boundary).Output
            consumer,
      ∀ occurrence,
        factor
            ⟨m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          (m14ArtProductionConsumersAt oldVisit sourceIndex boundary).read
            consumer occurrence :=
  (m14ArtProductionCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization consumer

theorem m14ArtProductionWork_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex
          boundary) → M14ArtWorkReadout,
      ∀ occurrence,
        factor
            ⟨m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          m14ArtProductionWorkReadAt occurrence :=
  (m14ArtProductionCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inl (.inr PUnit.unit))

theorem m14ArtProductionLifecycle_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex
          boundary) → M14ArtProductionLifecycleReadout,
      ∀ occurrence,
        factor
            ⟨m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          m14ArtProductionLifecycleReadAt occurrence :=
  (m14ArtProductionCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inr PUnit.unit)

theorem m14ArtProductionEveryCurrentReadout_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Output : Type*}
    (readout : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
      Output) :
    ∃! factor :
        Set.range (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex
          boundary) → Output,
      ∀ occurrence,
        factor
            ⟨m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ = readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (m14ArtProductionCultureFaceRead_injective oldVisit sourceIndex boundary)
    readout

theorem m14ArtProductionCompleteCarrier_uniqueIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Alternate : Type*}
    (alternate : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
      Alternate)
    (alternateExact : FaceKernelExactAt
      (m14ArtProductionConsumersAt oldVisit sourceIndex boundary) alternate) :
    ∃! equivalence :
        Set.range (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex
          boundary) ≃ Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ := by
  let canonical := m14ArtProductionCultureKernelExactAt oldVisit sourceIndex
    boundary
  refine ⟨canonical.completeCarrierEquiv alternateExact,
    canonical.completeCarrierEquiv_commutes alternateExact, ?_⟩
  intro candidate commutes
  exact canonical.completeCarrierEquiv_unique alternateExact candidate
    commutes

def m14ArtProductionRefinedNormalFormAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  refinedFace
    (refinedFace
      (m14ArtProductionOldTeachingFaceReadAt oldVisit sourceIndex boundary)
      (m14ArtProductionWorkIndependentReadoutAt oldVisit sourceIndex boundary))
    (m14ArtProductionLifecycleIndependentReadoutAt oldVisit sourceIndex
      boundary)

theorem m14ArtProductionRefinedNormalForm_kernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14ArtProductionConsumersAt oldVisit sourceIndex boundary)
      (m14ArtProductionRefinedNormalFormAt oldVisit sourceIndex boundary) :=
  (m14ArtProductionOldTeachingKernelExactAt oldVisit sourceIndex boundary
    ).adjoin_refinedFace.adjoin_refinedFace

theorem m14ArtProduction_sourceEquivNormalForm_uniqueAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex
          boundary) ≃
          Set.range (m14ArtProductionRefinedNormalFormAt oldVisit sourceIndex
            boundary),
      ∀ occurrence,
        equivalence
            ⟨m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨m14ArtProductionRefinedNormalFormAt oldVisit sourceIndex boundary
              occurrence,
            occurrence, rfl⟩ :=
  m14ArtProductionCompleteCarrier_uniqueIsoAt oldVisit sourceIndex boundary
    (m14ArtProductionRefinedNormalFormAt oldVisit sourceIndex boundary)
    (m14ArtProductionRefinedNormalForm_kernelExactAt oldVisit sourceIndex
      boundary)

theorem m14ArtProductionCultureRepresentation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    type_of% (sourceGeneratedM14ArtProductionCultureMaterial_directConsumer
      oldVisit sourceIndex boundary occurrence) ∧
      type_of% (m14ArtProductionCultureKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProductionCulture_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProductionCultureKernelExactAt oldVisit sourceIndex
        boundary) ∧
      Nonempty
        ((m14ArtProductionConsumersAt oldVisit sourceIndex boundary).Quotient ≃
          Set.range (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex
            boundary)) ∧
      (∀ consumer,
        type_of% (m14ArtProductionCultureEveryConsumer_uniqueFactorizationAt
          oldVisit sourceIndex boundary consumer)) ∧
      type_of% (m14ArtProductionWork_updatedUniqueFactorizationAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProductionLifecycle_updatedUniqueFactorizationAt
        oldVisit sourceIndex boundary) ∧
      type_of% (m14ArtProduction_sourceEquivNormalForm_uniqueAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProductionConsumer_grounded oldVisit sourceIndex
        boundary) :=
  ⟨sourceGeneratedM14ArtProductionCultureMaterial_directConsumer oldVisit
      sourceIndex boundary occurrence,
    m14ArtProductionCultureKernelEscapeAt oldVisit sourceIndex boundary,
    m14ArtProductionCulture_oldFactorization_isEmpty oldVisit sourceIndex
      boundary,
    m14ArtProductionCultureKernelExactAt oldVisit sourceIndex boundary,
    ⟨m14ArtProductionCultureQuotientEquivRangeAt oldVisit sourceIndex
      boundary⟩,
    m14ArtProductionCultureEveryConsumer_uniqueFactorizationAt oldVisit
      sourceIndex boundary,
    m14ArtProductionWork_updatedUniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14ArtProductionLifecycle_updatedUniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14ArtProduction_sourceEquivNormalForm_uniqueAt oldVisit sourceIndex
      boundary,
    m14ArtProductionConsumer_grounded oldVisit sourceIndex boundary⟩

end
end Representation
end ArtProduction
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.m14ArtProductionCultureKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.m14ArtProductionCultureKernelExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.m14ArtProductionCultureQuotientEquivRangeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.m14ArtProductionWork_updatedUniqueFactorizationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.m14ArtProductionCompleteCarrier_uniqueIsoAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.m14ArtProductionCultureRepresentation_directConsumer
