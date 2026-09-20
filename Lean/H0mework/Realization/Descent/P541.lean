import H0mework.Arithmetic.PrimeShadow.P540

/-!
# Proposition 541: unified hard gate v5 with descent-normal-form front door

P539 joined the physical source-accounting gate with the canonical
prime-indexed mathematical support gate.  P540 then constructed the canonical
descent quotient for the remaining Goldbach/H¹ prime shadow and showed that
the structured bridge reduces exactly to:

* descent predicate compatibility on the arithmetic-admissible domain;
* prime-indexed support of the quotient shadow.

This file pushes that normal form back to the unified front door.  It proves
that a strict physical producer plus the two descent obligations is enough to
produce the current structured grand front door and hence the current unified
producer output.

Boundary: this still does not prove the two descent obligations.  It removes
one more layer of arbitrary producer interface around them.
-/

noncomputable section

namespace SaturationMonoid

open AffineRelaxation
open AffineRelaxation.GeometryConnection
open StandardModelConstraint

universe u

/-! ## Unified hard gate v5 -/

/-- Unified hard gate v5: v4 plus the canonical descent producer normal form
from P540. -/
structure UnifiedGrandHardGateV5Certificate where
  base :
    UnifiedGrandHardGateV4Certificate.{u}
  descent :
    CanonicalDescentPrimeShadowProducerCertificate

/-- THEOREM 1: the unified hard gate v5 is inhabited by the current
machine-checked gates. -/
def unifiedGrandHardGateV5Certificate :
    UnifiedGrandHardGateV5Certificate.{u} where
  base := unifiedGrandHardGateV4Certificate
  descent := canonicalDescentPrimeShadowProducerCertificate

namespace UnifiedGrandHardGateV5Certificate

/-- THEOREM 2: v5 keeps the canonical descent-generated shadow equality. -/
theorem descent_generated_shadow_eq
    (G : UnifiedGrandHardGateV5Certificate.{u})
    (x : ArithmeticAdmissibleSevenFacet) :
    G.descent.producer.arithmeticShadow x.arithmetic =
      G.descent.producer.spectralShadow x.spectral :=
  G.descent.generated_shadow_eq x

/-- THEOREM 3: on the canonical descent producer, a concrete bridge is exactly
the descent-compatibility obligation. -/
theorem descent_concrete_bridge_iff_compatibility
    (G : UnifiedGrandHardGateV5Certificate.{u}) :
    Nonempty
        (ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge
          G.descent.producer) ↔
      DescentPredicateCompatible :=
  G.descent.concrete_bridge_iff_compatibility

/-- THEOREM 4: on the canonical descent producer, a structured bridge is
exactly descent compatibility plus prime-indexed support. -/
theorem descent_structured_bridge_iff
    (G : UnifiedGrandHardGateV5Certificate.{u}) :
    Nonempty
        (StructuredConcreteAdmissiblePrimeShadowBridge G.descent.producer) ↔
      DescentPredicateCompatible ∧
        Nonempty (PrimeIndexedShadowStructure G.descent.producer) :=
  G.descent.structured_bridge_iff

/-- THEOREM 5: the old `Prop` truth shadow remains rejected at the structured
front door. -/
theorem rejects_truth_value_shadow_front_door
    (G : UnifiedGrandHardGateV5Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A] :
    Not
      (Nonempty
        (UnifiedGrandStructuredProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry
          truthValuePrimeShadowProducer)) :=
  G.base.rejects_truth_value_shadow_front_door

/-- THEOREM 6: a strict physical producer plus the two canonical descent
obligations gives the structured unified front door for the descent producer. -/
def structuredFrontDoor_of_descent_obligations
    (_G : UnifiedGrandHardGateV5Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry)
    (physical :
      ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry)
    (hcompat : DescentPredicateCompatible)
    (hinj : DescentArithmeticPrimeCodeInjective) :
    UnifiedGrandStructuredProducerFrontDoor
      Index A CKMCarrier PhysicalGeometry
      descentEulerPrimeCouplingProducer where
  adapter := adapter
  physical := physical
  prime_shadow :=
    descentStructuredBridge_of_canonical_prime_code hcompat hinj

/-- THEOREM 7: the same inputs give the current unified producer output. -/
def unifiedOutput_of_descent_obligations
    (G : UnifiedGrandHardGateV5Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry)
    (physical :
      ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry)
    (hcompat : DescentPredicateCompatible)
    (hinj : DescentArithmeticPrimeCodeInjective) :
    UnifiedGrandProducerOutput
      Index A CKMCarrier descentEulerPrimeCouplingProducer :=
  unifiedGrandProducerOutput_of_structuredFrontDoor
    (G.structuredFrontDoor_of_descent_obligations
      adapter physical hcompat hinj)

/-- THEOREM 8: under the two descent obligations, the admissible-domain
Goldbach/H¹ synchronization used by the unified output is the P325 rate-level
statement. -/
theorem rateGoldbach_iff_h1_of_descent_obligations
    (_G : UnifiedGrandHardGateV5Certificate.{u})
    (hcompat : DescentPredicateCompatible)
    (hinj : DescentArithmeticPrimeCodeInjective)
    (x : ArithmeticAdmissibleSevenFacet) :
    HalfSigmaRateGoldbachComplete x.val.rate ↔
      H1SpectralNoObstructionComplete x.spectral := by
  exact
    (descentStructuredBridge_of_canonical_prime_code hcompat hinj).concrete
      |>.rateGoldbach_iff_h1_no_obstruction x

end UnifiedGrandHardGateV5Certificate

end SaturationMonoid
