import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer.IndependentM14UrbanSpatialConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.SourceGeneratedM14ArtProductionCultureRepresentation

/-!
# Source-generated M14 urban culture representation

The complete art-production culture face is constant on the blocked/restored
restrictions of one exact route root and crossing.  Independent accessibility
and capacity consumers distinguish them.  The source-generated urban face
closes the exact kernel before quotient, factorization or unique-iso results.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Urban
namespace Representation

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer

noncomputable section

structure SourceGeneratedM14UrbanCultureFaceAt (base : Nat) : Type where
  artProductionCulture : SourceGeneratedM14ArtProductionCultureFaceAt base
  routeAccessible : M14UrbanAccessibilityReadout
  exitCapacity : M14UrbanCapacityReadout

def m14UrbanOldArtProductionFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary →
      SourceGeneratedM14ArtProductionCultureFaceAt
        (m14InstitutionalBaseAt boundary) :=
  m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary ∘
    m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary

def m14UrbanCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14UrbanCultureFaceAt
      (m14InstitutionalBaseAt boundary) where
  artProductionCulture := m14UrbanOldArtProductionFaceReadAt oldVisit
    sourceIndex boundary occurrence
  routeAccessible := m14UrbanAccessibilityReadAt occurrence
  exitCapacity := m14UrbanCapacityReadAt occurrence

inductive SourceGeneratedM14UrbanCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type
  | private generated

def generateM14UrbanCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14UrbanCultureFaceTokenAt oldVisit sourceIndex boundary :=
  .generated

namespace SourceGeneratedM14UrbanCultureFaceTokenAt

def read
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_token : SourceGeneratedM14UrbanCultureFaceTokenAt oldVisit sourceIndex
      boundary)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14UrbanCultureFaceAt (m14InstitutionalBaseAt boundary) :=
  m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence

end SourceGeneratedM14UrbanCultureFaceTokenAt

structure SourceGeneratedM14UrbanCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  face : SourceGeneratedM14UrbanCultureFaceTokenAt oldVisit sourceIndex
    boundary
  faceExact : face = generateM14UrbanCultureFaceTokenAt oldVisit sourceIndex
    boundary (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary)
  artProductionMaterial : SourceGeneratedM14ArtProductionCultureMaterialAt
    oldVisit sourceIndex boundary
  artProductionMaterialExact : artProductionMaterial =
    sourceGeneratedM14ArtProductionCultureMaterialAt oldVisit sourceIndex
      boundary
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary)
  urbanSource : SourceGeneratedM14UrbanSpatialCoordinatesAt oldVisit
    sourceIndex boundary
  urbanSourceExact : urbanSource =
    sourceGeneratedM14UrbanSpatialCoordinatesAt oldVisit sourceIndex boundary

def sourceGeneratedM14UrbanCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14UrbanCultureMaterialAt oldVisit sourceIndex boundary where
  face := generateM14UrbanCultureFaceTokenAt oldVisit sourceIndex boundary
    occurrence
  faceExact := rfl
  artProductionMaterial :=
    sourceGeneratedM14ArtProductionCultureMaterialAt oldVisit sourceIndex
      boundary
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary)
  artProductionMaterialExact := rfl
  urbanSource := sourceGeneratedM14UrbanSpatialCoordinatesAt oldVisit
    sourceIndex boundary
  urbanSourceExact := rfl

@[simp] theorem m14UrbanCultureMaterial_faceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    (sourceGeneratedM14UrbanCultureMaterialAt oldVisit sourceIndex boundary
      occurrence).face.read occurrence =
      m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence :=
  rfl

theorem sourceGeneratedM14UrbanCultureMaterial_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    let material := sourceGeneratedM14UrbanCultureMaterialAt oldVisit
      sourceIndex boundary occurrence
    Nonempty (SourceGeneratedM14UrbanCultureMaterialAt oldVisit sourceIndex
        boundary) ∧
      material.face.read occurrence =
        m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence ∧
      material.artProductionMaterial =
        sourceGeneratedM14ArtProductionCultureMaterialAt oldVisit sourceIndex
          boundary
            (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex
              boundary) ∧
      material.urbanSource =
        sourceGeneratedM14UrbanSpatialCoordinatesAt oldVisit sourceIndex
          boundary ∧
      type_of% (sourceNativeM14UrbanSpatialCoordinates_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (m14UrbanSpatialConsumer_grounded oldVisit sourceIndex
        boundary) := by
  let material := sourceGeneratedM14UrbanCultureMaterialAt oldVisit sourceIndex
    boundary occurrence
  exact ⟨⟨material⟩, rfl, material.artProductionMaterialExact,
    material.urbanSourceExact,
    sourceNativeM14UrbanSpatialCoordinates_directConsumer oldVisit sourceIndex
      boundary,
    m14UrbanSpatialConsumer_grounded oldVisit sourceIndex boundary⟩

theorem m14UrbanOldArtProductionKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14UrbanReindexedArtProductionConsumersAt oldVisit sourceIndex boundary)
      (m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary) :=
  (m14ArtProductionCultureKernelExactAt oldVisit sourceIndex boundary).reindex
    (m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary)

@[simp] theorem m14UrbanOldArtProductionFace_blocked_eq_restored
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary
        (m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary) =
      m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary
        (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary) :=
  congrArg (m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary)
    (m14UrbanOldArtProductionView_blocked_eq_restored oldVisit sourceIndex
      boundary)

theorem m14UrbanCultureKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary)
      (m14UrbanAccessibilityIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary,
    m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary,
    m14UrbanOldArtProductionFace_blocked_eq_restored oldVisit sourceIndex
      boundary,
    (m14UrbanSpatialRead_blocked_ne_restored oldVisit sourceIndex boundary).1⟩

theorem m14UrbanCulture_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14UrbanAccessibilityReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary) :=
  (m14UrbanCultureKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14UrbanCultureFaceRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right sameFace
  apply m14UrbanAccessibilityRead_injective oldVisit sourceIndex boundary
  exact congrArg SourceGeneratedM14UrbanCultureFaceAt.routeAccessible sameFace

theorem m14UrbanCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14UrbanConsumersAt oldVisit sourceIndex boundary)
      (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right
  constructor
  · intro sameFace consumer
    cases consumer with
    | inl priorConsumer =>
        cases priorConsumer with
        | inl oldConsumer =>
            have sameOldFace := congrArg
              SourceGeneratedM14UrbanCultureFaceAt.artProductionCulture
              sameFace
            exact ((m14UrbanOldArtProductionKernelExactAt oldVisit sourceIndex
              boundary) left right).1 sameOldFace oldConsumer
        | inr _unit =>
            exact congrArg
              SourceGeneratedM14UrbanCultureFaceAt.routeAccessible sameFace
    | inr _unit =>
        exact congrArg SourceGeneratedM14UrbanCultureFaceAt.exitCapacity
          sameFace
  · intro sameConsumers
    have sameAccess := sameConsumers (.inl (.inr PUnit.unit))
    have sameOccurrence := m14UrbanAccessibilityRead_injective oldVisit
      sourceIndex boundary sameAccess
    subst right
    rfl

noncomputable def m14UrbanCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14UrbanConsumersAt oldVisit sourceIndex boundary).Quotient ≃
      Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) :=
  (m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary
    ).quotientEquivRange

theorem m14UrbanCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer : (m14UrbanConsumersAt oldVisit sourceIndex boundary).Consumer) :
    ∃! factor :
        Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) →
          (m14UrbanConsumersAt oldVisit sourceIndex boundary).Output consumer,
      ∀ occurrence,
        factor
            ⟨m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          (m14UrbanConsumersAt oldVisit sourceIndex boundary).read consumer
            occurrence :=
  (m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization consumer

theorem m14UrbanAccessibility_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) →
          M14UrbanAccessibilityReadout,
      ∀ occurrence,
        factor
            ⟨m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          m14UrbanAccessibilityReadAt occurrence :=
  (m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inl (.inr PUnit.unit))

theorem m14UrbanCapacity_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) →
          M14UrbanCapacityReadout,
      ∀ occurrence,
        factor
            ⟨m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          m14UrbanCapacityReadAt occurrence :=
  (m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inr PUnit.unit)

theorem m14UrbanEveryCurrentReadout_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Output : Type*}
    (readout : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary →
      Output) :
    ∃! factor :
        Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) →
          Output,
      ∀ occurrence,
        factor
            ⟨m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence,
              occurrence, rfl⟩ = readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (m14UrbanCultureFaceRead_injective oldVisit sourceIndex boundary) readout

theorem m14UrbanCompleteCarrier_uniqueIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Alternate : Type*}
    (alternate : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary →
      Alternate)
    (alternateExact : FaceKernelExactAt
      (m14UrbanConsumersAt oldVisit sourceIndex boundary) alternate) :
    ∃! equivalence :
        Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ := by
  let canonical := m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary
  refine ⟨canonical.completeCarrierEquiv alternateExact,
    canonical.completeCarrierEquiv_commutes alternateExact, ?_⟩
  intro candidate commutes
  exact canonical.completeCarrierEquiv_unique alternateExact candidate
    commutes

def m14UrbanRefinedNormalFormAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  refinedFace
    (refinedFace
      (m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary)
      (m14UrbanAccessibilityIndependentReadoutAt oldVisit sourceIndex boundary))
    (m14UrbanCapacityIndependentReadoutAt oldVisit sourceIndex boundary)

theorem m14UrbanRefinedNormalForm_kernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14UrbanConsumersAt oldVisit sourceIndex boundary)
      (m14UrbanRefinedNormalFormAt oldVisit sourceIndex boundary) :=
  (m14UrbanOldArtProductionKernelExactAt oldVisit sourceIndex boundary
    ).adjoin_refinedFace.adjoin_refinedFace

theorem m14Urban_sourceEquivNormalForm_uniqueAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range (m14UrbanRefinedNormalFormAt oldVisit sourceIndex boundary),
      ∀ occurrence,
        equivalence
            ⟨m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          ⟨m14UrbanRefinedNormalFormAt oldVisit sourceIndex boundary occurrence,
            occurrence, rfl⟩ :=
  m14UrbanCompleteCarrier_uniqueIsoAt oldVisit sourceIndex boundary
    (m14UrbanRefinedNormalFormAt oldVisit sourceIndex boundary)
    (m14UrbanRefinedNormalForm_kernelExactAt oldVisit sourceIndex boundary)

theorem m14UrbanCultureRepresentation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    type_of% (sourceGeneratedM14UrbanCultureMaterial_directConsumer oldVisit
      sourceIndex boundary occurrence) ∧
      type_of% (m14UrbanCultureKernelEscapeAt oldVisit sourceIndex boundary) ∧
      type_of% (m14UrbanCulture_oldFactorization_isEmpty oldVisit sourceIndex
        boundary) ∧
      type_of% (m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary) ∧
      Nonempty
        ((m14UrbanConsumersAt oldVisit sourceIndex boundary).Quotient ≃
          Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary)) ∧
      (∀ consumer,
        type_of% (m14UrbanCultureEveryConsumer_uniqueFactorizationAt oldVisit
          sourceIndex boundary consumer)) ∧
      type_of% (m14UrbanAccessibility_updatedUniqueFactorizationAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14UrbanCapacity_updatedUniqueFactorizationAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14Urban_sourceEquivNormalForm_uniqueAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14UrbanSpatialConsumer_grounded oldVisit sourceIndex
        boundary) :=
  ⟨sourceGeneratedM14UrbanCultureMaterial_directConsumer oldVisit sourceIndex
      boundary occurrence,
    m14UrbanCultureKernelEscapeAt oldVisit sourceIndex boundary,
    m14UrbanCulture_oldFactorization_isEmpty oldVisit sourceIndex boundary,
    m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary,
    ⟨m14UrbanCultureQuotientEquivRangeAt oldVisit sourceIndex boundary⟩,
    m14UrbanCultureEveryConsumer_uniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14UrbanAccessibility_updatedUniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14UrbanCapacity_updatedUniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14Urban_sourceEquivNormalForm_uniqueAt oldVisit sourceIndex boundary,
    m14UrbanSpatialConsumer_grounded oldVisit sourceIndex boundary⟩

end
end Representation
end Urban
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation.m14UrbanCultureKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation.m14UrbanCultureKernelExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation.m14UrbanCultureQuotientEquivRangeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation.m14UrbanAccessibility_updatedUniqueFactorizationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation.m14UrbanCompleteCarrier_uniqueIsoAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation.m14UrbanCultureRepresentation_directConsumer
