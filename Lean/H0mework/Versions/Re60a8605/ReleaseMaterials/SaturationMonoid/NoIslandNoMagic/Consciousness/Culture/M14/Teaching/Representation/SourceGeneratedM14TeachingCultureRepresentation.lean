import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer.IndependentM14TeachingConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source.SourceGeneratedM14StructuralClassPriceCultureMaterial

/-!
# Source-generated M14 teaching culture representation

The complete class-price face is constant on the exact source/target practice
of the material-action delivery.  Independently declared teaching
transmission and evaluation consumers distinguish the two sides.  Their
source-generated face closes the bidirectional kernel before quotient,
factorization or alternate-carrier equivalence is derived.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Teaching
namespace Representation

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer

noncomputable section

structure SourceGeneratedM14TeachingCultureFaceAt (base : Nat) : Type where
  classPriceCulture : SourceGeneratedM14StructuralClassPriceCultureFaceAt base
  teachingTransmission : M14TeachingTransmissionReadout
  teachingEvaluation : M14TeachingEffect

def m14TeachingOldClassPriceFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14TeachingOccurrenceAt oldVisit sourceIndex boundary →
      SourceGeneratedM14StructuralClassPriceCultureFaceAt
        (m14InstitutionalBaseAt boundary) :=
  m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex boundary ∘
    m14TeachingOldClassPriceViewAt oldVisit sourceIndex boundary

def m14TeachingCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14TeachingCultureFaceAt
      (m14InstitutionalBaseAt boundary) where
  classPriceCulture := m14TeachingOldClassPriceFaceReadAt oldVisit sourceIndex
    boundary occurrence
  teachingTransmission := m14TeachingTransmissionReadAt occurrence
  teachingEvaluation := m14TeachingEvaluationReadAt occurrence

inductive SourceGeneratedM14TeachingCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type
  | private generated

def generateM14TeachingCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14TeachingCultureFaceTokenAt oldVisit sourceIndex
      boundary :=
  .generated

namespace SourceGeneratedM14TeachingCultureFaceTokenAt

def read
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_token : SourceGeneratedM14TeachingCultureFaceTokenAt oldVisit sourceIndex
      boundary)
    (occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14TeachingCultureFaceAt
      (m14InstitutionalBaseAt boundary) :=
  m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary occurrence

end SourceGeneratedM14TeachingCultureFaceTokenAt

structure SourceGeneratedM14TeachingCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  face : SourceGeneratedM14TeachingCultureFaceTokenAt oldVisit sourceIndex
    boundary
  faceExact : face = generateM14TeachingCultureFaceTokenAt oldVisit sourceIndex
    boundary
      (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary)
  classPriceMaterial :
    SourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
      sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary)
  classPriceMaterialExact : classPriceMaterial =
    sourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
      sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary)
  teachingEvent : SourceGeneratedM14TeachingContactEventAt oldVisit sourceIndex
    boundary
  teachingEventExact : teachingEvent =
    sourceGeneratedM14TeachingContactEventAt oldVisit sourceIndex boundary

def sourceGeneratedM14TeachingCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14TeachingCultureMaterialAt oldVisit sourceIndex
      boundary where
  face := generateM14TeachingCultureFaceTokenAt oldVisit sourceIndex boundary
    occurrence
  faceExact := rfl
  classPriceMaterial :=
    sourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
      sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary)
  classPriceMaterialExact := rfl
  teachingEvent := sourceGeneratedM14TeachingContactEventAt oldVisit
    sourceIndex boundary
  teachingEventExact := rfl

@[simp] theorem m14TeachingCultureMaterial_faceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    (sourceGeneratedM14TeachingCultureMaterialAt oldVisit sourceIndex boundary
      occurrence).face.read occurrence =
      m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary occurrence :=
  rfl

theorem sourceGeneratedM14TeachingCultureMaterial_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    let material := sourceGeneratedM14TeachingCultureMaterialAt oldVisit
      sourceIndex boundary occurrence
    Nonempty (SourceGeneratedM14TeachingCultureMaterialAt oldVisit sourceIndex
        boundary) ∧
      material.face.read occurrence =
        m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary occurrence ∧
      material.classPriceMaterial =
        sourceGeneratedM14StructuralClassPriceCultureMaterialAt oldVisit
          sourceIndex boundary
            (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
              boundary) ∧
      material.teachingEvent =
        sourceGeneratedM14TeachingContactEventAt oldVisit sourceIndex boundary ∧
      type_of% (sourceGeneratedM14PlatformTeachingDelivery_directConsumer
        oldVisit sourceIndex boundary) ∧
      type_of% (m14TeachingConsumer_grounded oldVisit sourceIndex boundary) := by
  let material := sourceGeneratedM14TeachingCultureMaterialAt oldVisit
    sourceIndex boundary occurrence
  exact ⟨⟨material⟩, rfl, material.classPriceMaterialExact,
    material.teachingEventExact,
    sourceGeneratedM14PlatformTeachingDelivery_directConsumer oldVisit
      sourceIndex boundary,
    m14TeachingConsumer_grounded oldVisit sourceIndex boundary⟩

theorem m14TeachingOldClassPriceKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14TeachingReindexedClassPriceConsumersAt oldVisit sourceIndex boundary)
      (m14TeachingOldClassPriceFaceReadAt oldVisit sourceIndex boundary) :=
  (m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary
    ).reindex (m14TeachingOldClassPriceViewAt oldVisit sourceIndex boundary)

@[simp] theorem m14TeachingOldClassPriceFace_source_eq_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14TeachingOldClassPriceFaceReadAt oldVisit sourceIndex boundary
        (m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary) =
      m14TeachingOldClassPriceFaceReadAt oldVisit sourceIndex boundary
        (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary) :=
  congrArg
    (m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex boundary)
    (m14TeachingOldClassPriceView_source_eq_target oldVisit sourceIndex
      boundary)

theorem m14TeachingCultureKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14TeachingOldClassPriceFaceReadAt oldVisit sourceIndex boundary)
      (m14TeachingTransmissionIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14TeachingSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14TeachingOldClassPriceFace_source_eq_target oldVisit sourceIndex
      boundary,
    m14TeachingTransmissionRead_source_ne_target oldVisit sourceIndex
      boundary⟩

theorem m14TeachingCulture_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14TeachingTransmissionReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14TeachingOldClassPriceFaceReadAt oldVisit sourceIndex boundary) :=
  (m14TeachingCultureKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14TeachingCultureFaceRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right sameFace
  apply m14TeachingTransmissionRead_injective oldVisit sourceIndex boundary
  exact congrArg SourceGeneratedM14TeachingCultureFaceAt.teachingTransmission
    sameFace

theorem m14TeachingCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14TeachingConsumersAt oldVisit sourceIndex boundary)
      (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) := by
  intro left right
  constructor
  · intro sameFace consumer
    cases consumer with
    | inl priorConsumer =>
        cases priorConsumer with
        | inl oldConsumer =>
            have sameOldFace := congrArg
              SourceGeneratedM14TeachingCultureFaceAt.classPriceCulture
              sameFace
            exact ((m14TeachingOldClassPriceKernelExactAt oldVisit sourceIndex
              boundary) left right).1 sameOldFace oldConsumer
        | inr _unit =>
            exact congrArg
              SourceGeneratedM14TeachingCultureFaceAt.teachingTransmission
              sameFace
    | inr _unit =>
        exact congrArg
          SourceGeneratedM14TeachingCultureFaceAt.teachingEvaluation sameFace
  · intro sameConsumers
    have sameTransmission := sameConsumers (.inl (.inr PUnit.unit))
    have sameOccurrence := m14TeachingTransmissionRead_injective oldVisit
      sourceIndex boundary sameTransmission
    subst right
    rfl

noncomputable def m14TeachingCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14TeachingConsumersAt oldVisit sourceIndex boundary).Quotient ≃
      Set.range (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) :=
  (m14TeachingCultureKernelExactAt oldVisit sourceIndex boundary
    ).quotientEquivRange

theorem m14TeachingCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer : (m14TeachingConsumersAt oldVisit sourceIndex
      boundary).Consumer) :
    ∃! factor :
        Set.range (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) →
          (m14TeachingConsumersAt oldVisit sourceIndex boundary).Output
            consumer,
      ∀ occurrence,
        factor
            ⟨m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          (m14TeachingConsumersAt oldVisit sourceIndex boundary).read consumer
            occurrence :=
  (m14TeachingCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization consumer

theorem m14Teaching_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) →
          M14TeachingTransmissionReadout,
      ∀ occurrence,
        factor
            ⟨m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          m14TeachingTransmissionReadAt occurrence :=
  (m14TeachingCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inl (.inr PUnit.unit))

theorem m14TeachingEvaluation_updatedUniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! factor :
        Set.range (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) →
          M14TeachingEffect,
      ∀ occurrence,
        factor
            ⟨m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          m14TeachingEvaluationReadAt occurrence :=
  (m14TeachingCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization (.inr PUnit.unit)

theorem m14TeachingEveryCurrentReadout_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Output : Type*}
    (readout : M14TeachingOccurrenceAt oldVisit sourceIndex boundary → Output) :
    ∃! factor :
        Set.range (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) →
          Output,
      ∀ occurrence,
        factor
            ⟨m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ = readout occurrence :=
  FaceKernelExactAt.everyCurrentReadout_uniqueFactorization
    (m14TeachingCultureFaceRead_injective oldVisit sourceIndex boundary)
    readout

theorem m14TeachingCompleteCarrier_uniqueIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Alternate : Type*}
    (alternate : M14TeachingOccurrenceAt oldVisit sourceIndex boundary →
      Alternate)
    (alternateExact : FaceKernelExactAt
      (m14TeachingConsumersAt oldVisit sourceIndex boundary) alternate) :
    ∃! equivalence :
        Set.range (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range alternate,
      ∀ occurrence,
        equivalence
            ⟨m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨alternate occurrence, occurrence, rfl⟩ := by
  let canonical := m14TeachingCultureKernelExactAt oldVisit sourceIndex
    boundary
  refine ⟨canonical.completeCarrierEquiv alternateExact,
    canonical.completeCarrierEquiv_commutes alternateExact, ?_⟩
  intro candidate commutes
  exact canonical.completeCarrierEquiv_unique alternateExact candidate
    commutes

def m14TeachingRefinedNormalFormAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  refinedFace
    (refinedFace
      (m14TeachingOldClassPriceFaceReadAt oldVisit sourceIndex boundary)
      (m14TeachingTransmissionIndependentReadoutAt oldVisit sourceIndex
        boundary))
    (m14TeachingEvaluationIndependentReadoutAt oldVisit sourceIndex boundary)

theorem m14TeachingRefinedNormalForm_kernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14TeachingConsumersAt oldVisit sourceIndex boundary)
      (m14TeachingRefinedNormalFormAt oldVisit sourceIndex boundary) :=
  (m14TeachingOldClassPriceKernelExactAt oldVisit sourceIndex boundary
    ).adjoin_refinedFace.adjoin_refinedFace

theorem m14Teaching_sourceEquivNormalForm_uniqueAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range (m14TeachingRefinedNormalFormAt oldVisit sourceIndex
            boundary),
      ∀ occurrence,
        equivalence
            ⟨m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨m14TeachingRefinedNormalFormAt oldVisit sourceIndex boundary
              occurrence,
            occurrence, rfl⟩ :=
  m14TeachingCompleteCarrier_uniqueIsoAt oldVisit sourceIndex boundary
    (m14TeachingRefinedNormalFormAt oldVisit sourceIndex boundary)
    (m14TeachingRefinedNormalForm_kernelExactAt oldVisit sourceIndex boundary)

theorem m14TeachingCultureRepresentation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    type_of% (sourceGeneratedM14TeachingCultureMaterial_directConsumer oldVisit
      sourceIndex boundary occurrence) ∧
      type_of% (m14TeachingCultureKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14TeachingCulture_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14TeachingCultureKernelExactAt oldVisit sourceIndex
        boundary) ∧
      Nonempty
        ((m14TeachingConsumersAt oldVisit sourceIndex boundary).Quotient ≃
          Set.range
            (m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary)) ∧
      (∀ consumer,
        type_of% (m14TeachingCultureEveryConsumer_uniqueFactorizationAt
          oldVisit sourceIndex boundary consumer)) ∧
      type_of% (m14Teaching_updatedUniqueFactorizationAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14TeachingEvaluation_updatedUniqueFactorizationAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14Teaching_sourceEquivNormalForm_uniqueAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14TeachingConsumer_grounded oldVisit sourceIndex boundary) :=
  ⟨sourceGeneratedM14TeachingCultureMaterial_directConsumer oldVisit
      sourceIndex boundary occurrence,
    m14TeachingCultureKernelEscapeAt oldVisit sourceIndex boundary,
    m14TeachingCulture_oldFactorization_isEmpty oldVisit sourceIndex boundary,
    m14TeachingCultureKernelExactAt oldVisit sourceIndex boundary,
    ⟨m14TeachingCultureQuotientEquivRangeAt oldVisit sourceIndex boundary⟩,
    m14TeachingCultureEveryConsumer_uniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14Teaching_updatedUniqueFactorizationAt oldVisit sourceIndex boundary,
    m14TeachingEvaluation_updatedUniqueFactorizationAt oldVisit sourceIndex
      boundary,
    m14Teaching_sourceEquivNormalForm_uniqueAt oldVisit sourceIndex boundary,
    m14TeachingConsumer_grounded oldVisit sourceIndex boundary⟩

end
end Representation
end Teaching
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.m14TeachingCultureKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.m14TeachingCultureKernelExactAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.m14TeachingCultureQuotientEquivRangeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.m14Teaching_updatedUniqueFactorizationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.m14TeachingCompleteCarrier_uniqueIsoAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.m14TeachingCultureRepresentation_directConsumer
