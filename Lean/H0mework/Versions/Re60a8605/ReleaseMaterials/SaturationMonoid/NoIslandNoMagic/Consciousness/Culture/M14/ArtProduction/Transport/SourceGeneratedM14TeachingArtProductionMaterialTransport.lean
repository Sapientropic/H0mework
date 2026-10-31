import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.SourceGeneratedM14ArtProductionCultureRepresentation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Installation.SourceInstalledM14TeachingCultureFace

/-!
# Teaching root to art-production material-action transport

The teaching root's current `4` and the source-generated art material action
are different root occurrences.  Their exact singleton restrictions are
constructively presented, while a shared canonical full-admission receipt
proves common provenance.  The art material action retains its own next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ArtProduction
namespace Transport

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation

noncomputable section

abbrev M14TeachingArtProductionSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence :
      (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.actual.OccurrenceAt (4 : Nat) //
    occurrence =
      (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted 4 }

def m14TeachingArtProductionSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14TeachingArtProductionSourceNextOccurrenceAt oldVisit sourceIndex
      boundary :=
  ⟨(m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).emitted 4, rfl⟩

abbrev M14ArtProductionMaterialActionRestrictionAt (boundary : Nat) :=
  { occurrence : M14ArtProductionMaterialOccurrenceAt boundary //
    occurrence = m14ArtProductionMaterialOccurrenceAt boundary }

def m14ArtProductionMaterialActionRestrictionAt (boundary : Nat) :
    M14ArtProductionMaterialActionRestrictionAt boundary :=
  ⟨m14ArtProductionMaterialOccurrenceAt boundary, rfl⟩

def m14TeachingArtProductionMaterialPresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (M14TeachingArtProductionSourceNextOccurrenceAt oldVisit sourceIndex
        boundary)
      (M14ArtProductionMaterialActionRestrictionAt boundary) where
  forward := fun _source =>
    m14ArtProductionMaterialActionRestrictionAt boundary
  backward := fun _target =>
    m14TeachingArtProductionSourceNextOccurrenceAt oldVisit sourceIndex
      boundary
  backward_forward := by
    intro source
    apply Subtype.ext
    exact source.property.symm
  forward_backward := by
    intro target
    apply Subtype.ext
    exact target.property.symm

structure SourceGeneratedM14TeachingArtProductionMaterialTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  teachingNext : M14TeachingArtProductionSourceNextOccurrenceAt oldVisit
    sourceIndex boundary
  teachingNextExact : teachingNext =
    m14TeachingArtProductionSourceNextOccurrenceAt oldVisit sourceIndex
      boundary
  materialAction : M14ArtProductionMaterialActionRestrictionAt boundary
  materialActionExact : materialAction =
    m14ArtProductionMaterialActionRestrictionAt boundary
  occurrencePresentation : ConstructivePresentation
    (M14TeachingArtProductionSourceNextOccurrenceAt oldVisit sourceIndex
      boundary)
    (M14ArtProductionMaterialActionRestrictionAt boundary)
  occurrencePresentationExact : occurrencePresentation =
    m14TeachingArtProductionMaterialPresentationAt oldVisit sourceIndex
      boundary

def sourceGeneratedM14TeachingArtProductionMaterialTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14TeachingArtProductionMaterialTransportAt oldVisit
      sourceIndex boundary where
  teachingNext := m14TeachingArtProductionSourceNextOccurrenceAt oldVisit
    sourceIndex boundary
  teachingNextExact := rfl
  materialAction := m14ArtProductionMaterialActionRestrictionAt boundary
  materialActionExact := rfl
  occurrencePresentation := m14TeachingArtProductionMaterialPresentationAt
    oldVisit sourceIndex boundary
  occurrencePresentationExact := rfl

@[simp] theorem m14TeachingArtProductionMaterialPresentation_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14TeachingArtProductionMaterialPresentationAt oldVisit sourceIndex
      boundary).forward
        (m14TeachingArtProductionSourceNextOccurrenceAt oldVisit sourceIndex
          boundary) =
      (sourceGeneratedM14TeachingArtProductionMaterialTransportAt oldVisit
        sourceIndex boundary).materialAction :=
  rfl

theorem m14TeachingArtProduction_commonFullAdmission
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionSourceAt oldVisit sourceIndex boundary).fullAdmission =
      (sourceGeneratedM14ArtProductionCultureMaterialAt oldVisit sourceIndex
        boundary
          (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary)
        ).teachingMaterial.teachingEvent.fullAdmission :=
  rfl

theorem sourceGeneratedM14TeachingArtProductionMaterialTransport_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let transport :=
      sourceGeneratedM14TeachingArtProductionMaterialTransportAt oldVisit
        sourceIndex boundary
    Nonempty (SourceGeneratedM14TeachingArtProductionMaterialTransportAt
        oldVisit sourceIndex boundary) ∧
      transport.occurrencePresentation.forward transport.teachingNext =
        transport.materialAction ∧
      type_of% (m14TeachingCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 3) ∧
      type_of% (m14ArtProduction_actionOccurrence_exact boundary) ∧
      type_of% (m14ArtProduction_sourceActionRuntime oldVisit sourceIndex
        boundary) ∧
      type_of% (m14TeachingArtProduction_commonFullAdmission oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProductionMaterialActionNext_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProductionCultureRepresentation_directConsumer oldVisit
        sourceIndex boundary
          (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex
            boundary)) := by
  let transport :=
    sourceGeneratedM14TeachingArtProductionMaterialTransportAt oldVisit
      sourceIndex boundary
  exact ⟨⟨transport⟩, rfl,
    m14TeachingCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary
      3,
    m14ArtProduction_actionOccurrence_exact boundary,
    m14ArtProduction_sourceActionRuntime oldVisit sourceIndex boundary,
    m14TeachingArtProduction_commonFullAdmission oldVisit sourceIndex boundary,
    m14ArtProductionMaterialActionNext_exact oldVisit sourceIndex boundary,
    m14ArtProductionCultureRepresentation_directConsumer oldVisit sourceIndex
      boundary
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary)⟩

end
end Transport
end ArtProduction
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Transport.m14TeachingArtProductionMaterialPresentationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Transport.m14TeachingArtProductionMaterialPresentation_commutes
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Transport.m14TeachingArtProduction_commonFullAdmission
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Transport.sourceGeneratedM14TeachingArtProductionMaterialTransport_directConsumer
