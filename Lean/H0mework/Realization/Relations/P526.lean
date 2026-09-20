import H0mework.Arithmetic.PrimeShadow.P518
import H0mework.Physics.YukawaSources.P525

/-!
# Proposition 526: structured front-door exclusion for truth-value shadows

P518 proves the local gate: a `Prop`-valued truth shadow cannot carry an
injective prime-indexed support, so it is not a structured concrete admissible
prime-shadow bridge.

This file pushes that gate up to the P516/P518 unified producer front door.  It
prevents the strongest current unified output interface from being satisfied by
the tautological truth-value shadow.  In other words, a structured grand
producer must bring a real prime-indexed carrier; the target theorem's truth
value is not enough.
-/

noncomputable section

namespace SaturationMonoid

open AffineRelaxation

universe u

/-! ## Structured front-door consequences -/

/-- THEOREM 1: every structured unified front door exposes a faithful
prime-indexed shadow carrier. -/
def UnifiedGrandStructuredProducerFrontDoor.toPrimeIndexedShadow
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    {P : AffineRelaxation.EulerPrimeCouplingProducers}
    (F :
      UnifiedGrandStructuredProducerFrontDoor
        Index A CKMCarrier PhysicalGeometry P) :
    AffineRelaxation.PrimeIndexedShadowStructure P :=
  F.prime_shadow.prime_indexed

/-- THEOREM 2: the `Prop`-valued truth shadow cannot satisfy the structured
unified producer front door. -/
theorem truthValuePrimeShadowProducer_no_structuredFrontDoor
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A] :
    Not
      (Nonempty
        (UnifiedGrandStructuredProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry
          AffineRelaxation.truthValuePrimeShadowProducer)) := by
  rintro ⟨F⟩
  exact
    AffineRelaxation.truthValuePrimeShadowProducer_not_structuredBridge
      ⟨F.prime_shadow⟩

/-- Compact certificate that the structured front door rejects tautological
truth-value shadows. -/
structure StructuredFrontDoorTruthShadowExclusionCertificate where
  structured_front_door_to_prime_indexed :
    ∀ {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A],
      ∀ {P : AffineRelaxation.EulerPrimeCouplingProducers},
        UnifiedGrandStructuredProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry P ->
          AffineRelaxation.PrimeIndexedShadowStructure P
  truth_shadow_rejected :
    ∀ {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A],
      Not
        (Nonempty
          (UnifiedGrandStructuredProducerFrontDoor
            Index A CKMCarrier PhysicalGeometry
            AffineRelaxation.truthValuePrimeShadowProducer))

/-- THEOREM 3: the canonical structured-front-door truth-shadow exclusion
certificate. -/
def structuredFrontDoorTruthShadowExclusionCertificate :
    StructuredFrontDoorTruthShadowExclusionCertificate.{u} where
  structured_front_door_to_prime_indexed := by
    intro Index A CKMCarrier PhysicalGeometry hA P F
    exact F.toPrimeIndexedShadow
  truth_shadow_rejected := by
    intro Index A CKMCarrier PhysicalGeometry hA
    exact
      truthValuePrimeShadowProducer_no_structuredFrontDoor
        (Index := Index)
        (A := A)
        (CKMCarrier := CKMCarrier)
        (PhysicalGeometry := PhysicalGeometry)

end SaturationMonoid
