import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation.SourceGeneratedM14UrbanCultureRepresentation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation.SourceInstalledM14ArtProductionCultureFace

/-!
# Art-production root to urban route-root transport

The art-production root's current `5` and the periodic urban route event are
different root occurrences.  Exact singleton restrictions are connected by a
constructive presentation.  The urban route root is independently proved to
be the same refusal-target Payment root retained by the nested class-price
source chain; no ambient root equality is claimed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Urban
namespace Transport

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14ProofCarryingPeriodicRouteOutageRestorationRegression
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation

noncomputable section

abbrev M14ArtUrbanSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence :
      (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.actual.OccurrenceAt (5 : Nat) //
    occurrence =
      (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted 5 }

def m14ArtUrbanSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary :=
  ⟨(m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).emitted 5, rfl⟩

abbrev M14UrbanRouteRootRestrictionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : type_of%
      (m14UrbanRouteRestorationAt oldVisit sourceIndex boundary).rootOccurrence //
    occurrence =
      (m14UrbanRouteRestorationAt oldVisit sourceIndex boundary).rootOccurrence }

def m14UrbanRouteRootRestrictionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14UrbanRouteRootRestrictionAt oldVisit sourceIndex boundary :=
  ⟨(m14UrbanRouteRestorationAt oldVisit sourceIndex boundary).rootOccurrence,
    rfl⟩

def m14ArtUrbanRoutePresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (M14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary)
      (M14UrbanRouteRootRestrictionAt oldVisit sourceIndex boundary) where
  forward := fun _source =>
    m14UrbanRouteRootRestrictionAt oldVisit sourceIndex boundary
  backward := fun _target =>
    m14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary
  backward_forward := by
    intro source
    apply Subtype.ext
    exact source.property.symm
  forward_backward := by
    intro target
    apply Subtype.ext
    exact target.property.symm

structure SourceGeneratedM14ArtUrbanRouteTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  artNext : M14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary
  artNextExact : artNext =
    m14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary
  routeRoot : M14UrbanRouteRootRestrictionAt oldVisit sourceIndex boundary
  routeRootExact : routeRoot =
    m14UrbanRouteRootRestrictionAt oldVisit sourceIndex boundary
  occurrencePresentation : ConstructivePresentation
    (M14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary)
    (M14UrbanRouteRootRestrictionAt oldVisit sourceIndex boundary)
  occurrencePresentationExact : occurrencePresentation =
    m14ArtUrbanRoutePresentationAt oldVisit sourceIndex boundary

def sourceGeneratedM14ArtUrbanRouteTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14ArtUrbanRouteTransportAt oldVisit sourceIndex
      boundary where
  artNext := m14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary
  artNextExact := rfl
  routeRoot := m14UrbanRouteRootRestrictionAt oldVisit sourceIndex boundary
  routeRootExact := rfl
  occurrencePresentation := m14ArtUrbanRoutePresentationAt oldVisit
    sourceIndex boundary
  occurrencePresentationExact := rfl

@[simp] theorem m14ArtUrbanRoutePresentation_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtUrbanRoutePresentationAt oldVisit sourceIndex boundary).forward
        (m14ArtUrbanSourceNextOccurrenceAt oldVisit sourceIndex boundary) =
      (sourceGeneratedM14ArtUrbanRouteTransportAt oldVisit sourceIndex boundary
        ).routeRoot :=
  rfl

theorem m14ArtUrban_commonTargetPaymentSource
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14UrbanRouteRestorationAt oldVisit sourceIndex boundary).rootOccurrence =
        (m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary
          ).rootOccurrence ∧
      (sourceGeneratedM14UrbanCultureMaterialAt oldVisit sourceIndex boundary
        (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary)
        ).artProductionMaterial.teachingMaterial.classPriceMaterial.coordinates =
        sourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
          sourceIndex boundary :=
  ⟨m14UrbanRouteRoot_eq_refusalTargetPaymentRoot oldVisit sourceIndex boundary,
    rfl⟩

theorem sourceGeneratedM14ArtUrbanRouteTransport_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let transport := sourceGeneratedM14ArtUrbanRouteTransportAt oldVisit
      sourceIndex boundary
    Nonempty (SourceGeneratedM14ArtUrbanRouteTransportAt oldVisit sourceIndex
        boundary) ∧
      transport.occurrencePresentation.forward transport.artNext =
        transport.routeRoot ∧
      type_of% (m14ArtProductionCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 4) ∧
      type_of% (m14ArtUrban_commonTargetPaymentSource oldVisit sourceIndex
        boundary) ∧
      type_of% (periodicRouteRootLedgerAndNextExact
        (m14UrbanDepthAt oldVisit sourceIndex boundary)) ∧
      type_of% (m14UrbanCultureRepresentation_directConsumer oldVisit
        sourceIndex boundary
          (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary)) := by
  let transport := sourceGeneratedM14ArtUrbanRouteTransportAt oldVisit
    sourceIndex boundary
  exact ⟨⟨transport⟩, rfl,
    m14ArtProductionCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
      boundary 4,
    m14ArtUrban_commonTargetPaymentSource oldVisit sourceIndex boundary,
    periodicRouteRootLedgerAndNextExact
      (m14UrbanDepthAt oldVisit sourceIndex boundary),
    m14UrbanCultureRepresentation_directConsumer oldVisit sourceIndex boundary
      (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary)⟩

end
end Transport
end Urban
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Transport.m14ArtUrbanRoutePresentationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Transport.m14ArtUrbanRoutePresentation_commutes
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Transport.m14ArtUrban_commonTargetPaymentSource
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Transport.sourceGeneratedM14ArtUrbanRouteTransport_directConsumer
