import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.SourceGeneratedM14TeachingCultureRepresentation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation.SourceInstalledM14StructuralClassPriceCultureFace

/-!
# Class-price root to teaching material-action transport

The class-price root's current `3` and the renewed platform material action
belong to different roots.  Their exact singleton restrictions are connected
by a constructive presentation while both native receipts are retained.  The
material action supplies the teaching contact and its own generated next;
neither is identified with the class-price root evolution.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Teaching
namespace Transport

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation

noncomputable section

abbrev M14ClassPriceTeachingSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence :
      (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).toRoot.actual.OccurrenceAt (3 : Nat) //
    occurrence =
      (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 3 }

def m14ClassPriceTeachingSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14ClassPriceTeachingSourceNextOccurrenceAt oldVisit sourceIndex
      boundary :=
  ⟨(m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
    boundary).emitted 3, rfl⟩

abbrev M14TeachingMaterialActionRestrictionAt (boundary : Nat) :=
  { occurrence : M14TeachingMaterialOccurrenceAt boundary //
    occurrence = m14TeachingMaterialOccurrenceAt boundary }

def m14TeachingMaterialActionRestrictionAt (boundary : Nat) :
    M14TeachingMaterialActionRestrictionAt boundary :=
  ⟨m14TeachingMaterialOccurrenceAt boundary, rfl⟩

def m14ClassPriceTeachingMaterialPresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (M14ClassPriceTeachingSourceNextOccurrenceAt oldVisit sourceIndex
        boundary)
      (M14TeachingMaterialActionRestrictionAt boundary) where
  forward := fun _source => m14TeachingMaterialActionRestrictionAt boundary
  backward := fun _target =>
    m14ClassPriceTeachingSourceNextOccurrenceAt oldVisit sourceIndex boundary
  backward_forward := by
    intro source
    apply Subtype.ext
    exact source.property.symm
  forward_backward := by
    intro target
    apply Subtype.ext
    exact target.property.symm

structure SourceGeneratedM14ClassPriceTeachingMaterialTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  classPriceNext : M14ClassPriceTeachingSourceNextOccurrenceAt oldVisit
    sourceIndex boundary
  classPriceNextExact : classPriceNext =
    m14ClassPriceTeachingSourceNextOccurrenceAt oldVisit sourceIndex boundary
  materialAction : M14TeachingMaterialActionRestrictionAt boundary
  materialActionExact : materialAction =
    m14TeachingMaterialActionRestrictionAt boundary
  occurrencePresentation : ConstructivePresentation
    (M14ClassPriceTeachingSourceNextOccurrenceAt oldVisit sourceIndex boundary)
    (M14TeachingMaterialActionRestrictionAt boundary)
  occurrencePresentationExact : occurrencePresentation =
    m14ClassPriceTeachingMaterialPresentationAt oldVisit sourceIndex boundary

def sourceGeneratedM14ClassPriceTeachingMaterialTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14ClassPriceTeachingMaterialTransportAt oldVisit
      sourceIndex boundary where
  classPriceNext := m14ClassPriceTeachingSourceNextOccurrenceAt oldVisit
    sourceIndex boundary
  classPriceNextExact := rfl
  materialAction := m14TeachingMaterialActionRestrictionAt boundary
  materialActionExact := rfl
  occurrencePresentation := m14ClassPriceTeachingMaterialPresentationAt
    oldVisit sourceIndex boundary
  occurrencePresentationExact := rfl

@[simp] theorem m14ClassPriceTeachingMaterialPresentation_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ClassPriceTeachingMaterialPresentationAt oldVisit sourceIndex boundary
      ).forward
        (m14ClassPriceTeachingSourceNextOccurrenceAt oldVisit sourceIndex
          boundary) =
      (sourceGeneratedM14ClassPriceTeachingMaterialTransportAt oldVisit
        sourceIndex boundary).materialAction :=
  rfl

/-- Both sides descend from the same canonical full-admission receipt.  The
class-price side reaches it through refusal and institutional source material;
the teaching side reads it from the exact material-action event. -/
theorem m14ClassPriceTeaching_commonFullAdmission
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (sourceGeneratedM14TeachingContactEventAt oldVisit sourceIndex boundary
      ).fullAdmission =
      (sourceGeneratedM14TeachingCultureMaterialAt oldVisit sourceIndex
        boundary
          (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary)
        ).classPriceMaterial.refusalMaterial.institutionalMaterial.fullAdmission :=
  rfl

theorem sourceGeneratedM14ClassPriceTeachingMaterialTransport_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let transport :=
      sourceGeneratedM14ClassPriceTeachingMaterialTransportAt oldVisit
        sourceIndex boundary
    Nonempty (SourceGeneratedM14ClassPriceTeachingMaterialTransportAt oldVisit
        sourceIndex boundary) ∧
      transport.occurrencePresentation.forward transport.classPriceNext =
        transport.materialAction ∧
      type_of% (m14StructuralClassPriceCulture_generatedNextCurrentAt_eq
        oldVisit sourceIndex boundary 2) ∧
      type_of% (m14TeachingContact_actionOccurrence_exact boundary) ∧
      type_of% (m14TeachingContact_sourceActionRuntime oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ClassPriceTeaching_commonFullAdmission oldVisit sourceIndex
        boundary) ∧
      type_of% (m14TeachingMaterialActionNext_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14TeachingCultureRepresentation_directConsumer oldVisit
        sourceIndex boundary
          (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary)) := by
  let transport :=
    sourceGeneratedM14ClassPriceTeachingMaterialTransportAt oldVisit
      sourceIndex boundary
  exact ⟨⟨transport⟩, rfl,
    m14StructuralClassPriceCulture_generatedNextCurrentAt_eq oldVisit
      sourceIndex boundary 2,
    m14TeachingContact_actionOccurrence_exact boundary,
    m14TeachingContact_sourceActionRuntime oldVisit sourceIndex boundary,
    m14ClassPriceTeaching_commonFullAdmission oldVisit sourceIndex boundary,
    m14TeachingMaterialActionNext_exact oldVisit sourceIndex boundary,
    m14TeachingCultureRepresentation_directConsumer oldVisit sourceIndex
      boundary (m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary)⟩

end
end Transport
end Teaching
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Transport.m14ClassPriceTeachingMaterialPresentationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Transport.m14ClassPriceTeachingMaterialPresentation_commutes
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Transport.sourceGeneratedM14ClassPriceTeachingMaterialTransport_directConsumer
