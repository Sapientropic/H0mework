import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer.IndependentM14StructuralClassPriceConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source.SourceGeneratedM14RefusalCultureMaterial

/-!
# Source-generated structural class-price culture material

The new face joins the complete refusal culture target with two independent
readouts of one source-generated structural-rent occurrence: class position
and price/capture position.  The high source retains the exact target Payment,
relationship event, recurrence, periodic rent and exploitation witness.

No consumer coverage, quotient, factorization, root installation or future
is accepted by the producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ClassPrice
namespace Source

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer

noncomputable section

structure SourceGeneratedM14StructuralClassPriceCultureFaceAt
    (base : Nat) : Type where
  refusalCulture : SourceGeneratedM14RefusalCultureFaceAt base
  structuralClass : M14StructuralActor
  structuralPrice : M14StructuralPriceReadout

def m14StructuralClassPriceCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    SourceGeneratedM14StructuralClassPriceCultureFaceAt
      (m14InstitutionalBaseAt boundary) where
  refusalCulture :=
    m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary
      (m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary
        occurrence)
  structuralClass := m14StructuralClassReadAt occurrence
  structuralPrice := m14StructuralPriceReadAt occurrence

inductive SourceGeneratedM14StructuralClassPriceCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) : Type
  | private generated

def generateM14StructuralClassPriceCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    SourceGeneratedM14StructuralClassPriceCultureFaceTokenAt oldVisit
      sourceIndex boundary occurrence :=
  .generated

namespace SourceGeneratedM14StructuralClassPriceCultureFaceTokenAt

def read
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary}
    (_token : SourceGeneratedM14StructuralClassPriceCultureFaceTokenAt oldVisit
      sourceIndex boundary occurrence) :
    SourceGeneratedM14StructuralClassPriceCultureFaceAt
      (m14InstitutionalBaseAt boundary) :=
  m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex boundary
    occurrence

end SourceGeneratedM14StructuralClassPriceCultureFaceTokenAt

structure SourceGeneratedM14StructuralClassPriceCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) : Type 32 where
  private mk ::
  face : SourceGeneratedM14StructuralClassPriceCultureFaceTokenAt oldVisit
    sourceIndex boundary occurrence
  faceExact : face = generateM14StructuralClassPriceCultureFaceTokenAt
    oldVisit sourceIndex boundary occurrence
  refusalMaterial : SourceGeneratedM14RefusalCultureMaterialAt oldVisit
    sourceIndex boundary
      (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary)
  refusalMaterialExact : refusalMaterial =
    sourceGeneratedM14RefusalCultureMaterialAt oldVisit sourceIndex boundary
      (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary)
  coordinates : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
    sourceIndex boundary
  coordinatesExact : coordinates =
    sourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit sourceIndex
      boundary

def sourceGeneratedM14StructuralClassPriceCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    SourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
      sourceIndex boundary occurrence where
  face := generateM14StructuralClassPriceCultureFaceTokenAt oldVisit
    sourceIndex boundary occurrence
  faceExact := rfl
  refusalMaterial := sourceGeneratedM14RefusalCultureMaterialAt oldVisit
    sourceIndex boundary
      (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary)
  refusalMaterialExact := rfl
  coordinates := sourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
    sourceIndex boundary
  coordinatesExact := rfl

@[simp] theorem m14StructuralClassPriceCultureMaterial_faceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    (sourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
      sourceIndex boundary occurrence).face.read =
      m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex boundary
        occurrence :=
  rfl

theorem sourceGeneratedM14StructuralClassPriceCultureMaterial_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    let material :=
      sourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
        sourceIndex boundary occurrence
    Nonempty (SourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
        sourceIndex boundary occurrence) ∧
      material.face.read =
        m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex boundary
          occurrence ∧
      material.refusalMaterial =
        sourceGeneratedM14RefusalCultureMaterialAt oldVisit sourceIndex
          boundary
            (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary) ∧
      material.coordinates =
        sourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
          sourceIndex boundary ∧
      type_of% (m14StructuralClassPriceOccurrences_samePaymentAndEvent
        oldVisit sourceIndex boundary) ∧
      type_of% (sourceNativeM14StructuralClassPriceCoordinates_directConsumer
        oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceConsumer_grounded oldVisit sourceIndex
        boundary) ∧
      type_of% (m14StructuralClassPriceNoForgery_directConsumer oldVisit
        sourceIndex boundary) := by
  let material :=
    sourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
      sourceIndex boundary occurrence
  exact ⟨⟨material⟩, rfl, material.refusalMaterialExact,
    material.coordinatesExact,
    m14StructuralClassPriceOccurrences_samePaymentAndEvent oldVisit
      sourceIndex boundary,
    sourceNativeM14StructuralClassPriceCoordinates_directConsumer oldVisit
      sourceIndex boundary,
    m14StructuralClassPriceConsumer_grounded oldVisit sourceIndex boundary,
    m14StructuralClassPriceNoForgery_directConsumer oldVisit sourceIndex
      boundary⟩

end
end Source
end ClassPrice
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source.m14StructuralClassPriceCultureMaterial_faceRead_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source.sourceGeneratedM14StructuralClassPriceCultureMaterial_directConsumer
