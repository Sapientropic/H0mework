import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Interface.SourceNativeM14UrbanSpatialCoordinates
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation.SourceGeneratedM14ArtProductionCultureRepresentation

/-!
# Independent M14 urban spatial consumers

Blocked and restored route restrictions share the same exact route root and
crossing.  The complete art-production face is constant across them.  Route
accessibility and exit-capacity consumers are declared independently before
the urban carrier, quotient or root installation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Urban
namespace Consumer

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14ProofCarryingPeriodicRouteOutageRestorationRegression
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Interface

noncomputable section

def m14UrbanOldArtProductionViewAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary →
      M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary :=
  fun _occurrence =>
    m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary

def m14UrbanAccessibilityIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14UrbanAccessibilityReadout
  read := m14UrbanAccessibilityReadAt

def m14UrbanCapacityIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14UrbanCapacityReadout
  read := m14UrbanCapacityReadAt

def m14UrbanReindexedArtProductionConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionConsumersAt oldVisit sourceIndex boundary).reindex
    (m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary)

def m14UrbanAccessibilityConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14UrbanReindexedArtProductionConsumersAt oldVisit sourceIndex boundary
    ).adjoin
      (m14UrbanAccessibilityIndependentReadoutAt oldVisit sourceIndex boundary)

def m14UrbanConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14UrbanAccessibilityConsumersAt oldVisit sourceIndex boundary).adjoin
    (m14UrbanCapacityIndependentReadoutAt oldVisit sourceIndex boundary)

@[simp] theorem m14UrbanOldArtProductionView_blocked_eq_restored
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary
        (m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary) =
      m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary
        (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary) :=
  rfl

theorem m14UrbanAccessibilityKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary)
      (m14UrbanAccessibilityIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary,
    m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary,
    m14UrbanOldArtProductionView_blocked_eq_restored oldVisit sourceIndex
      boundary,
    (m14UrbanSpatialRead_blocked_ne_restored oldVisit sourceIndex boundary).1⟩

theorem m14UrbanCapacityKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary)
      (m14UrbanCapacityIndependentReadoutAt oldVisit sourceIndex boundary) :=
  ⟨m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary,
    m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary,
    m14UrbanOldArtProductionView_blocked_eq_restored oldVisit sourceIndex
      boundary,
    (m14UrbanSpatialRead_blocked_ne_restored oldVisit sourceIndex boundary).2⟩

theorem m14UrbanAccessibility_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14UrbanAccessibilityReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary) :=
  (m14UrbanAccessibilityKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14UrbanCapacity_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14UrbanCapacityReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14UrbanOldArtProductionViewAt oldVisit sourceIndex boundary) :=
  (m14UrbanCapacityKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14UrbanRetypingNoForgery_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceNativeM14UrbanSpatialCoordinates_directConsumer oldVisit
      sourceIndex boundary) ∧
      type_of% periodicRouteAuthorityAndRetypingControls ∧
      type_of% (periodicRouteSourceAndActionExact
        (m14UrbanDepthAt oldVisit sourceIndex boundary)) ∧
      type_of% (periodicRouteRootLedgerAndNextExact
        (m14UrbanDepthAt oldVisit sourceIndex boundary)) ∧
      type_of% (periodicRouteRestoresTheMissingAxis
        (m14UrbanDepthAt oldVisit sourceIndex boundary)) :=
  ⟨sourceNativeM14UrbanSpatialCoordinates_directConsumer oldVisit sourceIndex
      boundary,
    periodicRouteAuthorityAndRetypingControls,
    periodicRouteSourceAndActionExact
      (m14UrbanDepthAt oldVisit sourceIndex boundary),
    periodicRouteRootLedgerAndNextExact
      (m14UrbanDepthAt oldVisit sourceIndex boundary),
    periodicRouteRestoresTheMissingAxis
      (m14UrbanDepthAt oldVisit sourceIndex boundary)⟩

theorem m14UrbanSpatialConsumer_grounded
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
        (m14UrbanAccessibilityReadAt (oldVisit := oldVisit)
          (sourceIndex := sourceIndex) (boundary := boundary)) ∧
      Function.Injective
        (m14UrbanCapacityReadAt (oldVisit := oldVisit)
          (sourceIndex := sourceIndex) (boundary := boundary)) ∧
      type_of% (m14UrbanAccessibilityKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14UrbanCapacityKernelEscapeAt oldVisit sourceIndex boundary) ∧
      type_of% (m14UrbanAccessibility_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14UrbanCapacity_oldFactorization_isEmpty oldVisit sourceIndex
        boundary) ∧
      type_of% (m14UrbanRetypingNoForgery_directConsumer oldVisit sourceIndex
        boundary) :=
  ⟨m14UrbanAccessibilityRead_injective oldVisit sourceIndex boundary,
    m14UrbanCapacityRead_injective oldVisit sourceIndex boundary,
    m14UrbanAccessibilityKernelEscapeAt oldVisit sourceIndex boundary,
    m14UrbanCapacityKernelEscapeAt oldVisit sourceIndex boundary,
    m14UrbanAccessibility_oldFactorization_isEmpty oldVisit sourceIndex
      boundary,
    m14UrbanCapacity_oldFactorization_isEmpty oldVisit sourceIndex boundary,
    m14UrbanRetypingNoForgery_directConsumer oldVisit sourceIndex boundary⟩

end
end Consumer
end Urban
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer.m14UrbanAccessibilityKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer.m14UrbanCapacityKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer.m14UrbanRetypingNoForgery_directConsumer
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer.m14UrbanSpatialConsumer_grounded
