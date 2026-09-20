import H0mework.Arithmetic.PrimeProjection.P517

/-!
# Proposition 518: prime-indexed shadows are the non-tautological producer gate

P517 ruled out the easiest fake producer: the common shadow cannot merely be
the truth value of the target Goldbach/H1 predicate.

This file turns that warning into a structural gate.  A genuine Euler-side
prime shadow must still remember the prime-indexed support supplied by P322:
there must be an injective code from `PrimeExponent` into the common shadow.

The gate is deliberately modest.  It does not prove Goldbach, RH, or the final
Goldbach/H1 faithful pullback.  It proves that the next producer is required
to carry nontrivial prime-indexed structure, and that the `Prop`-valued
truth-shadow cannot pass this gate: proposition extensionality collapses
`Prop` to at most true/false values, so it cannot faithfully encode the three
distinct prime exponents `2`, `3`, and `5`.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Prime-indexed shadow structure -/

/-- A common prime shadow is structurally nontrivial when the prime-indexed
support can be faithfully read inside the shadow.  This is the minimal
Euler-product requirement: the shadow must carry the prime index, not only a
truth value of the desired theorem. -/
structure PrimeIndexedShadowStructure
    (P : EulerPrimeCouplingProducers) where
  primeCode : PrimeExponent -> P.PrimeShadow
  primeCode_injective : Function.Injective primeCode

/-- A structured concrete admissible bridge is a P325 concrete bridge plus
the prime-indexed support required above. -/
structure StructuredConcreteAdmissiblePrimeShadowBridge
    (P : EulerPrimeCouplingProducers) where
  concrete :
    ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P
  prime_indexed : PrimeIndexedShadowStructure P

namespace StructuredConcreteAdmissiblePrimeShadowBridge

/-- THEOREM 1: forgetting the prime-indexed structure recovers the P325
concrete admissible bridge used by P516. -/
def toConcrete {P : EulerPrimeCouplingProducers}
    (B : StructuredConcreteAdmissiblePrimeShadowBridge P) :
    ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P :=
  B.concrete

/-- THEOREM 2: any structured bridge synchronizes concrete Goldbach and H1
no-obstruction on the admissible seven-facet domain. -/
theorem goldbach_iff_h1_no_obstruction
    {P : EulerPrimeCouplingProducers}
    (B : StructuredConcreteAdmissiblePrimeShadowBridge P)
    (x : ArithmeticAdmissibleSevenFacet) :
    HalfSigmaImageGoldbachComplete x.arithmetic ↔
      H1SpectralNoObstructionComplete x.spectral :=
  B.concrete.goldbach_iff_h1_no_obstruction x

end StructuredConcreteAdmissiblePrimeShadowBridge

/-! ## The truth-value shadow cannot be prime-indexed -/

private theorem primeTwo_ne_primeThree : primeTwo ≠ primeThree := by
  intro h
  have hval : (primeTwo : PrimeExponent).1 = (primeThree : PrimeExponent).1 :=
    congrArg Subtype.val h
  norm_num [primeTwo, primeThree] at hval

private theorem primeTwo_ne_primeFive : primeTwo ≠ primeFive := by
  intro h
  have hval : (primeTwo : PrimeExponent).1 = (primeFive : PrimeExponent).1 :=
    congrArg Subtype.val h
  norm_num [primeTwo, primeFive] at hval

private theorem primeThree_ne_primeFive : primeThree ≠ primeFive := by
  intro h
  have hval :
      (primeThree : PrimeExponent).1 = (primeFive : PrimeExponent).1 :=
    congrArg Subtype.val h
  norm_num [primeThree, primeFive] at hval

private theorem prop_eq_of_true {P Q : Prop} (hP : P) (hQ : Q) :
    P = Q :=
  propext ⟨fun _ => hQ, fun _ => hP⟩

private theorem prop_eq_of_false {P Q : Prop} (hP : Not P) (hQ : Not Q) :
    P = Q :=
  propext ⟨fun h => False.elim (hP h), fun h => False.elim (hQ h)⟩

/-- THEOREM 3: no function from prime exponents to `Prop` can be injective.
With `propext`, all true propositions are equal and all false propositions
are equal, so the three primes `2`, `3`, and `5` force a collision. -/
theorem no_injective_primeExponent_to_Prop :
    Not (∃ f : PrimeExponent -> Prop, Function.Injective f) := by
  rintro ⟨f, hf⟩
  by_cases h2 : f primeTwo
  · by_cases h3 : f primeThree
    · have heq : f primeTwo = f primeThree :=
        prop_eq_of_true h2 h3
      exact primeTwo_ne_primeThree (hf heq)
    · by_cases h5 : f primeFive
      · have heq : f primeTwo = f primeFive :=
          prop_eq_of_true h2 h5
        exact primeTwo_ne_primeFive (hf heq)
      · have heq : f primeThree = f primeFive :=
          prop_eq_of_false h3 h5
        exact primeThree_ne_primeFive (hf heq)
  · by_cases h3 : f primeThree
    · by_cases h5 : f primeFive
      · have heq : f primeThree = f primeFive :=
          prop_eq_of_true h3 h5
        exact primeThree_ne_primeFive (hf heq)
      · have heq : f primeTwo = f primeFive :=
          prop_eq_of_false h2 h5
        exact primeTwo_ne_primeFive (hf heq)
    · have heq : f primeTwo = f primeThree :=
        prop_eq_of_false h2 h3
      exact primeTwo_ne_primeThree (hf heq)

/-- THEOREM 4: the P517 truth-value shadow cannot carry a faithful
prime-indexed support. -/
theorem truthValuePrimeShadowProducer_not_primeIndexed :
    Not (Nonempty (PrimeIndexedShadowStructure truthValuePrimeShadowProducer)) := by
  rintro ⟨S⟩
  exact no_injective_primeExponent_to_Prop
    ⟨S.primeCode, S.primeCode_injective⟩

/-- THEOREM 5: consequently, the truth-value shadow cannot be a structured
concrete admissible bridge. -/
theorem truthValuePrimeShadowProducer_not_structuredBridge :
    Not
      (Nonempty
        (StructuredConcreteAdmissiblePrimeShadowBridge
          truthValuePrimeShadowProducer)) := by
  rintro ⟨B⟩
  exact truthValuePrimeShadowProducer_not_primeIndexed
    ⟨B.prime_indexed⟩

/-- Compact certificate for the non-tautological prime-shadow gate. -/
structure PrimeIndexedShadowGateCertificate where
  structured_implies_concrete :
    ∀ {P : EulerPrimeCouplingProducers},
      StructuredConcreteAdmissiblePrimeShadowBridge P ->
        ArithmeticAdmissibleSevenFacet.ConcreteAdmissiblePrimeShadowBridge P
  no_prop_prime_index :
    Not (∃ f : PrimeExponent -> Prop, Function.Injective f)
  truth_value_shadow_not_prime_indexed :
    Not (Nonempty (PrimeIndexedShadowStructure truthValuePrimeShadowProducer))
  truth_value_shadow_not_structured :
    Not
      (Nonempty
        (StructuredConcreteAdmissiblePrimeShadowBridge
          truthValuePrimeShadowProducer))

/-- THEOREM 6: the canonical non-tautological gate certificate. -/
def primeIndexedShadowGateCertificate :
    PrimeIndexedShadowGateCertificate where
  structured_implies_concrete := by
    intro P B
    exact B.toConcrete
  no_prop_prime_index := no_injective_primeExponent_to_Prop
  truth_value_shadow_not_prime_indexed :=
    truthValuePrimeShadowProducer_not_primeIndexed
  truth_value_shadow_not_structured :=
    truthValuePrimeShadowProducer_not_structuredBridge

end AffineRelaxation

/-! ## Structured producer front door for the unified output -/

open AffineRelaxation
open AffineRelaxation.GeometryConnection
open StandardModelConstraint

/-- The P516 unified front door with the mathematical input strengthened from
an arbitrary concrete bridge to a prime-indexed structured bridge. -/
structure UnifiedGrandStructuredProducerFrontDoor
    (Index A CKMCarrier PhysicalGeometry : Type*) [AddCommGroup A]
    (P : AffineRelaxation.EulerPrimeCouplingProducers) where
  adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry
  physical :
    ExistsStrictPhysicalMatrixUnifiedProducer
      Index A CKMCarrier PhysicalGeometry
  prime_shadow :
    AffineRelaxation.StructuredConcreteAdmissiblePrimeShadowBridge P

/-- THEOREM 7: a structured front door forgets to the P516 front door. -/
def UnifiedGrandStructuredProducerFrontDoor.toFrontDoor
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    {P : AffineRelaxation.EulerPrimeCouplingProducers}
    (F :
      UnifiedGrandStructuredProducerFrontDoor
        Index A CKMCarrier PhysicalGeometry P) :
    UnifiedGrandProducerFrontDoor
      Index A CKMCarrier PhysicalGeometry P where
  adapter := F.adapter
  physical := F.physical
  prime_shadow := F.prime_shadow.toConcrete

/-- THEOREM 8: the stronger structured front door still yields the full P516
unified output.  The extra content is that the remaining mathematical
producer must be genuinely prime-indexed. -/
def unifiedGrandProducerOutput_of_structuredFrontDoor
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    {P : AffineRelaxation.EulerPrimeCouplingProducers}
    (F :
      UnifiedGrandStructuredProducerFrontDoor
        Index A CKMCarrier PhysicalGeometry P) :
    UnifiedGrandProducerOutput Index A CKMCarrier P :=
  unifiedGrandProducerOutput_of_frontDoor F.toFrontDoor

end SaturationMonoid
