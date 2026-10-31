import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation.SourceGeneratedM14StructuralClassPriceCultureRepresentation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation.SourceInstalledM14RefusalCultureFace

/-!
# Refusal-root to structural class-price target-Payment transport

The refusal root's current `2` occurrence and the next-cycle external Payment
belong to different roots and are not identified.  The former is the native
successor generated after installing the refusal face; the latter is the
actual refusal target Payment, definitionally the periodic Payment on which
structural rent is generated.

This module presents their exact singleton restrictions and retains both
source receipts.  It creates no ambient occurrence equality, projection
coface, quotient or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ClassPrice
namespace Transport

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation

noncomputable section

abbrev M14RefusalStructuralClassPriceSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence :
      (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.actual.OccurrenceAt (2 : Nat) //
    occurrence =
      (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted 2 }

def m14RefusalStructuralClassPriceSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit sourceIndex
      boundary :=
  ⟨(m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).emitted 2, rfl⟩

abbrev M14StructuralClassPriceTargetPaymentRestrictionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { payment : type_of%
      (m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary) //
    payment =
      m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary }

def m14StructuralClassPriceTargetPaymentRestrictionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14StructuralClassPriceTargetPaymentRestrictionAt oldVisit sourceIndex
      boundary :=
  ⟨m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary,
    rfl⟩

def m14RefusalStructuralClassPriceNextPresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (M14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit
        sourceIndex boundary)
      (M14StructuralClassPriceTargetPaymentRestrictionAt oldVisit sourceIndex
        boundary) where
  forward := fun _source =>
    m14StructuralClassPriceTargetPaymentRestrictionAt oldVisit sourceIndex
      boundary
  backward := fun _target =>
    m14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit sourceIndex
      boundary
  backward_forward := by
    intro source
    apply Subtype.ext
    exact source.property.symm
  forward_backward := by
    intro target
    apply Subtype.ext
    exact target.property.symm

structure SourceGeneratedM14RefusalStructuralClassPriceNextTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  refusalNext : M14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit
    sourceIndex boundary
  refusalNextExact : refusalNext =
    m14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit sourceIndex
      boundary
  targetPayment : M14StructuralClassPriceTargetPaymentRestrictionAt oldVisit
    sourceIndex boundary
  targetPaymentExact : targetPayment =
    m14StructuralClassPriceTargetPaymentRestrictionAt oldVisit sourceIndex
      boundary
  occurrencePresentation : ConstructivePresentation
    (M14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit sourceIndex
      boundary)
    (M14StructuralClassPriceTargetPaymentRestrictionAt oldVisit sourceIndex
      boundary)
  occurrencePresentationExact : occurrencePresentation =
    m14RefusalStructuralClassPriceNextPresentationAt oldVisit sourceIndex
      boundary

def sourceGeneratedM14RefusalStructuralClassPriceNextTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14RefusalStructuralClassPriceNextTransportAt oldVisit
      sourceIndex boundary where
  refusalNext :=
    m14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit sourceIndex
      boundary
  refusalNextExact := rfl
  targetPayment :=
    m14StructuralClassPriceTargetPaymentRestrictionAt oldVisit sourceIndex
      boundary
  targetPaymentExact := rfl
  occurrencePresentation :=
    m14RefusalStructuralClassPriceNextPresentationAt oldVisit sourceIndex
      boundary
  occurrencePresentationExact := rfl

@[simp] theorem m14RefusalStructuralClassPriceNextPresentation_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14RefusalStructuralClassPriceNextPresentationAt oldVisit sourceIndex
      boundary).forward
        (m14RefusalStructuralClassPriceSourceNextOccurrenceAt oldVisit
          sourceIndex boundary) =
      (sourceGeneratedM14RefusalStructuralClassPriceNextTransportAt oldVisit
        sourceIndex boundary).targetPayment :=
  rfl

theorem sourceGeneratedM14RefusalStructuralClassPriceNextTransport_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let transport :=
      sourceGeneratedM14RefusalStructuralClassPriceNextTransportAt oldVisit
        sourceIndex boundary
    Nonempty
        (SourceGeneratedM14RefusalStructuralClassPriceNextTransportAt oldVisit
          sourceIndex boundary) ∧
      transport.occurrencePresentation.forward transport.refusalNext =
        transport.targetPayment ∧
      type_of% (m14RefusalCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 1) ∧
      type_of% (m14StructuralClassPriceTargetPayment_eq_periodic oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceTargetPayment_rootExact oldVisit
        sourceIndex boundary) ∧
      Nonempty (SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCultureRepresentation_directConsumer
        oldVisit sourceIndex boundary
          (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
            boundary)) := by
  let transport :=
    sourceGeneratedM14RefusalStructuralClassPriceNextTransportAt oldVisit
      sourceIndex boundary
  exact ⟨⟨transport⟩, rfl,
    m14RefusalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary 1,
    m14StructuralClassPriceTargetPayment_eq_periodic oldVisit sourceIndex
      boundary,
    m14StructuralClassPriceTargetPayment_rootExact oldVisit sourceIndex
      boundary,
    ⟨sourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit sourceIndex
      boundary⟩,
    m14StructuralClassPriceCultureRepresentation_directConsumer oldVisit
      sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary)⟩

end
end Transport
end ClassPrice
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Transport.m14RefusalStructuralClassPriceNextPresentationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Transport.m14RefusalStructuralClassPriceNextPresentation_commutes
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Transport.sourceGeneratedM14RefusalStructuralClassPriceNextTransport_directConsumer
