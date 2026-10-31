import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface.SourceNativeM14StructuralClassPriceCoordinates
import H0mework.Foundation.Relations.ConsumerQuotient

/-!
# Independent structural class and price consumers

The complete refusal culture face is restricted to the exact paid-successor
target from which the structural-rent occurrence is generated.  Controller
and affected positions therefore have the same old refusal face, Payment and
relationship event.  Two independently defined consumers read the generated
class actor and price/capture position before any class-price carrier exists.

The negative mouths are existing source no-gos: reverse control and debt,
uncaptured payment, full fulfillment, and coarse protected-interest
reconstruction cannot manufacture the new position.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ClassPrice
namespace Consumer

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Relationship Renewal UBI.Capture
open ProcessGame.Society.M8RelationshipMaintenanceFixture
open ProcessGame.Society.M8RelationshipMaintenanceRenewalRegression
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14EssentialAccessSectorRegression
open ProcessGame.Society.M14StructuralRentCaptureRegression
open ProcessGame.Society.M14StructuralExploitationWitness
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface

noncomputable section

/-- Both structural positions are dependent faces of the same refusal target;
the complete prior carrier therefore sees the same actual target face. -/
def m14StructuralClassPriceOldRefusalViewAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary →
      M14RefusalOccurrenceAt oldVisit sourceIndex boundary :=
  fun _occurrence =>
    m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary

def m14StructuralClassIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14StructuralActor
  read := m14StructuralClassReadAt

def m14StructuralPriceIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14StructuralPriceReadout
  read := m14StructuralPriceReadAt

def m14StructuralClassPriceReindexedRefusalConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary).reindex
    (m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary)

def m14StructuralClassConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceReindexedRefusalConsumersAt oldVisit sourceIndex
    boundary).adjoin
      (m14StructuralClassIndependentReadoutAt oldVisit sourceIndex boundary)

def m14StructuralClassPriceConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassConsumersAt oldVisit sourceIndex boundary).adjoin
    (m14StructuralPriceIndependentReadoutAt oldVisit sourceIndex boundary)

@[simp] theorem m14StructuralClassPriceOldRefusalView_source_eq_target
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary
        (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
          boundary) =
      m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary) :=
  rfl

theorem m14StructuralClassKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary)
      (m14StructuralClassIndependentReadoutAt oldVisit sourceIndex boundary) :=
  ⟨m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14StructuralClassPriceOldRefusalView_source_eq_target oldVisit sourceIndex
      boundary,
    (m14StructuralClassPriceRead_hasActualDifference oldVisit sourceIndex
      boundary).1⟩

theorem m14StructuralPriceKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary)
      (m14StructuralPriceIndependentReadoutAt oldVisit sourceIndex boundary) :=
  ⟨m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex boundary,
    m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex boundary,
    m14StructuralClassPriceOldRefusalView_source_eq_target oldVisit sourceIndex
      boundary,
    (m14StructuralClassPriceRead_hasActualDifference oldVisit sourceIndex
      boundary).2⟩

theorem m14StructuralClass_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14StructuralClassReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary) :=
  (m14StructuralClassKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14StructuralPrice_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14StructuralPriceReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14StructuralClassPriceOldRefusalViewAt oldVisit sourceIndex boundary) :=
  (m14StructuralPriceKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

/-- Existing source mouths reject every shortcut that would turn an
uncontrolled, uncaptured, fulfilled or coarsely observed payment into the
structural class-price face. -/
theorem m14StructuralClassPriceNoForgery_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceNativeM14StructuralClassPriceCoordinates_directConsumer
      oldVisit sourceIndex boundary) ∧
      type_of% noForwardControl_noStructuralExploitationWitness ∧
      type_of% noForwardDebt_noStructuralExploitationWitness ∧
      IsEmpty UncapturedStructuralExploitationWitnessForgery ∧
      IsEmpty FullyFulfilledStructuralExploitationWitnessForgery ∧
      IsEmpty (FulfilledStructuralRentForgery
        (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)) ∧
      (¬ ∃ reconstruct :
          ProcessGame.Society.M3FiniteExchangeFixture.V.ProtectedInterest →
            EssentialAccessRelationAuthority,
        Function.LeftInverse reconstruct
          protectedInterestReadout) :=
  ⟨sourceNativeM14StructuralClassPriceCoordinates_directConsumer oldVisit
      sourceIndex boundary,
    noForwardControl_noStructuralExploitationWitness,
    noForwardDebt_noStructuralExploitationWitness,
    uncapturedStructuralExploitationWitnessForgery_isEmpty,
    fullyFulfilledStructuralExploitationWitnessForgery_isEmpty,
    fulfilledStructuralRentForgery_isEmpty
      (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary),
    ProcessGame.Society.M14EssentialAccessSectorRegression.no_protectedInterest_authority_reconstruction⟩

theorem m14StructuralClassPriceConsumer_grounded
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
        (m14StructuralClassReadAt (oldVisit := oldVisit)
          (sourceIndex := sourceIndex) (boundary := boundary)) ∧
      type_of% (m14StructuralClassKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14StructuralPriceKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14StructuralClass_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralPrice_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceNoForgery_directConsumer oldVisit
        sourceIndex boundary) :=
  ⟨m14StructuralClassRead_injective oldVisit sourceIndex boundary,
    m14StructuralClassKernelEscapeAt oldVisit sourceIndex boundary,
    m14StructuralPriceKernelEscapeAt oldVisit sourceIndex boundary,
    m14StructuralClass_oldFactorization_isEmpty oldVisit sourceIndex boundary,
    m14StructuralPrice_oldFactorization_isEmpty oldVisit sourceIndex boundary,
    m14StructuralClassPriceNoForgery_directConsumer oldVisit sourceIndex
      boundary⟩

end
end Consumer
end ClassPrice
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer.m14StructuralClassKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer.m14StructuralPriceKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer.m14StructuralClassPriceNoForgery_directConsumer
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer.m14StructuralClassPriceConsumer_grounded
