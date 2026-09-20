import H0mework.Arithmetic.PrimeShadow.P518
import H0mework.Realization.Fibres.P537

/-!
# Proposition 538: canonical prime-indexed support for the remaining producer

P517/P518 ruled out the fake mathematical close: a common prime shadow cannot
merely be the truth value of the desired Goldbach/H¹ theorem.  P537 then
packaged the Goldbach/RH side as a prescribed path rather than a claimed proof.

This file tightens the remaining producer spine one more turn.  The
non-tautological prime shadow has a canonical generator: `PrimeExponent`
itself.  In the category of prime-indexed supports, this generator is initial:
every genuine support receives exactly one support-preserving map from it.

Consequences:

* the final common shadow must carry at least the full prime-indexed support;
* no binary shadow (`Fin 2`, and hence no yes/no quotient) can faithfully encode
  that support;
* every structured admissible bridge inherits that non-binary obligation.

Boundary: this still does not construct the final concrete admissible
prime-shadow bridge, nor prove Goldbach/RH.  It proves the canonical minimum
shape any such bridge must pass through.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Generic prime-indexed supports -/

/-- A shadow type carries prime-indexed support when the prime exponents inject
into it.  This abstracts the P518 producer-specific field. -/
structure PrimeIndexedSupport (Shadow : Type*) where
  primeCode : PrimeExponent -> Shadow
  primeCode_injective : Function.Injective primeCode

namespace PrimeIndexedSupport

/-- The P518 producer-specific prime-indexed support, seen as the generic
support object. -/
def ofProducer {P : EulerPrimeCouplingProducers}
    (S : PrimeIndexedShadowStructure P) :
    PrimeIndexedSupport P.PrimeShadow where
  primeCode := S.primeCode
  primeCode_injective := S.primeCode_injective

/-- The canonical support: the prime exponents code themselves. -/
def canonical : PrimeIndexedSupport PrimeExponent where
  primeCode := id
  primeCode_injective := by
    intro p q h
    exact h

/-- A morphism of prime-indexed supports preserves the named prime code. -/
structure Hom {A B : Type*}
    (SA : PrimeIndexedSupport A) (SB : PrimeIndexedSupport B) where
  map : A -> B
  commutes : ∀ p : PrimeExponent, map (SA.primeCode p) = SB.primeCode p

namespace Hom

@[ext] theorem ext {A B : Type*}
    {SA : PrimeIndexedSupport A} {SB : PrimeIndexedSupport B}
    {f g : Hom SA SB}
    (h : f.map = g.map) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

end Hom

/-- The unique map out of the canonical prime support into any other
prime-indexed support. -/
def canonicalTo {Shadow : Type*} (S : PrimeIndexedSupport Shadow) :
    Hom canonical S where
  map := S.primeCode
  commutes := by
    intro p
    rfl

/-- THEOREM 1: `PrimeExponent` is initial among prime-indexed supports.

This is the formal version of "the final shadow must at least carry the prime
index, and that requirement has a canonical source rather than an arbitrary
case split." -/
theorem canonical_initial {Shadow : Type*}
    (S : PrimeIndexedSupport Shadow)
    (f : Hom canonical S) :
    f = canonicalTo S := by
  apply Hom.ext
  funext p
  exact f.commutes p

end PrimeIndexedSupport

/-! ## Binary shadows cannot carry the canonical support -/

theorem primeTwo_ne_primeThree' : primeTwo ≠ primeThree := by
  intro h
  have hval : (primeTwo : PrimeExponent).1 = (primeThree : PrimeExponent).1 :=
    congrArg Subtype.val h
  norm_num [primeTwo, primeThree] at hval

theorem primeTwo_ne_primeFive' : primeTwo ≠ primeFive := by
  intro h
  have hval : (primeTwo : PrimeExponent).1 = (primeFive : PrimeExponent).1 :=
    congrArg Subtype.val h
  norm_num [primeTwo, primeFive] at hval

theorem primeThree_ne_primeFive' : primeThree ≠ primeFive := by
  intro h
  have hval :
      (primeThree : PrimeExponent).1 = (primeFive : PrimeExponent).1 :=
    congrArg Subtype.val h
  norm_num [primeThree, primeFive] at hval

private theorem fin_two_eq_zero_or_one (x : Fin 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- THEOREM 2: no binary carrier can faithfully encode the prime exponents.
This is the `Fin 2` version of P518's `Prop` obstruction. -/
theorem no_injective_primeExponent_to_fin_two :
    Not (∃ f : PrimeExponent -> Fin 2, Function.Injective f) := by
  rintro ⟨f, hf⟩
  rcases fin_two_eq_zero_or_one (f primeTwo) with h2 | h2
  · rcases fin_two_eq_zero_or_one (f primeThree) with h3 | h3
    · have heq : f primeTwo = f primeThree := by rw [h2, h3]
      exact primeTwo_ne_primeThree' (hf heq)
    · rcases fin_two_eq_zero_or_one (f primeFive) with h5 | h5
      · have heq : f primeTwo = f primeFive := by rw [h2, h5]
        exact primeTwo_ne_primeFive' (hf heq)
      · have heq : f primeThree = f primeFive := by rw [h3, h5]
        exact primeThree_ne_primeFive' (hf heq)
  · rcases fin_two_eq_zero_or_one (f primeThree) with h3 | h3
    · rcases fin_two_eq_zero_or_one (f primeFive) with h5 | h5
      · have heq : f primeThree = f primeFive := by rw [h3, h5]
        exact primeThree_ne_primeFive' (hf heq)
      · have heq : f primeTwo = f primeFive := by rw [h2, h5]
        exact primeTwo_ne_primeFive' (hf heq)
    · have heq : f primeTwo = f primeThree := by rw [h2, h3]
      exact primeTwo_ne_primeThree' (hf heq)

/-- THEOREM 3: once a shadow carries prime-indexed support, it cannot be
faithfully compressed into a binary carrier. -/
theorem no_binary_coding_of_primeIndexedSupport
    {Shadow : Type*} (S : PrimeIndexedSupport Shadow) :
    Not (∃ encode : Shadow -> Fin 2, Function.Injective encode) := by
  rintro ⟨encode, hencode⟩
  apply no_injective_primeExponent_to_fin_two
  refine ⟨fun p => encode (S.primeCode p), ?_⟩
  intro p q h
  apply S.primeCode_injective
  exact hencode h

/-- THEOREM 4: every P518 producer-specific prime-indexed shadow inherits the
same non-binary obligation. -/
theorem no_binary_coding_of_primeIndexedShadowStructure
    {P : EulerPrimeCouplingProducers}
    (S : PrimeIndexedShadowStructure P) :
    Not (∃ encode : P.PrimeShadow -> Fin 2, Function.Injective encode) :=
  no_binary_coding_of_primeIndexedSupport (PrimeIndexedSupport.ofProducer S)

/-- THEOREM 5: every structured concrete admissible bridge has a prime shadow
that cannot be faithfully binary-coded. -/
theorem no_binary_coding_of_structuredBridge
    {P : EulerPrimeCouplingProducers}
    (B : StructuredConcreteAdmissiblePrimeShadowBridge P) :
    Not (∃ encode : P.PrimeShadow -> Fin 2, Function.Injective encode) :=
  no_binary_coding_of_primeIndexedShadowStructure B.prime_indexed

/-! ## Consequence for the unified structured front door -/

open StandardModelConstraint

/-- The mathematical shadow attached to a structured grand-producer front door,
forgetting all physical fields and retaining only its prime-indexed support. -/
def structuredFrontDoorPrimeIndexedSupport
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    {P : EulerPrimeCouplingProducers}
    (F :
      SaturationMonoid.UnifiedGrandStructuredProducerFrontDoor
        Index A CKMCarrier PhysicalGeometry P) :
    PrimeIndexedSupport P.PrimeShadow :=
  PrimeIndexedSupport.ofProducer F.prime_shadow.prime_indexed

/-- THEOREM 6: every structured grand-producer front door receives the unique
canonical map from `PrimeExponent` into its mathematical shadow. -/
def structuredFrontDoorCanonicalPrimeMap
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    {P : EulerPrimeCouplingProducers}
    (F :
      SaturationMonoid.UnifiedGrandStructuredProducerFrontDoor
        Index A CKMCarrier PhysicalGeometry P) :
    PrimeIndexedSupport.Hom
      PrimeIndexedSupport.canonical
      (structuredFrontDoorPrimeIndexedSupport F) :=
  PrimeIndexedSupport.canonicalTo (structuredFrontDoorPrimeIndexedSupport F)

/-- THEOREM 7: the structured grand-producer front door itself cannot have a
binary mathematical shadow.  This pushes the P518/P538 gate all the way to the
unified producer input. -/
theorem no_binary_coding_of_structuredFrontDoor
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    {P : EulerPrimeCouplingProducers}
    (F :
      SaturationMonoid.UnifiedGrandStructuredProducerFrontDoor
        Index A CKMCarrier PhysicalGeometry P) :
    Not (∃ encode : P.PrimeShadow -> Fin 2, Function.Injective encode) :=
  no_binary_coding_of_structuredBridge F.prime_shadow

/-! ## Packaged tightening certificate -/

/-- Compact certificate for the canonical prime-indexed producer spine. -/
structure CanonicalPrimeIndexedProducerSpineCertificate where
  root_object_count :
    Fintype.card SaturationMonoid.CoreMathematicalObject18 = 18
  root_goldbach_rh_path :
    SaturationMonoid.GoldbachRHPrescribedPathCertificate
  canonical_support :
    PrimeIndexedSupport PrimeExponent
  canonical_initial :
    ∀ {Shadow : Type*} (S : PrimeIndexedSupport Shadow)
      (f : PrimeIndexedSupport.Hom PrimeIndexedSupport.canonical S),
      f = PrimeIndexedSupport.canonicalTo S
  no_binary_prime_support :
    Not (∃ f : PrimeExponent -> Fin 2, Function.Injective f)
  no_binary_supported_shadow :
    ∀ {Shadow : Type*} (_ : PrimeIndexedSupport Shadow),
      Not (∃ encode : Shadow -> Fin 2, Function.Injective encode)
  no_binary_structured_bridge :
    ∀ {P : EulerPrimeCouplingProducers}
      (_ : StructuredConcreteAdmissiblePrimeShadowBridge P),
      Not (∃ encode : P.PrimeShadow -> Fin 2, Function.Injective encode)
  no_binary_structured_front_door :
    ∀ {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
      {P : EulerPrimeCouplingProducers}
      (_ :
        SaturationMonoid.UnifiedGrandStructuredProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry P),
      Not (∃ encode : P.PrimeShadow -> Fin 2, Function.Injective encode)

/-- THEOREM 6: the canonical prime-indexed producer spine certificate. -/
def canonicalPrimeIndexedProducerSpineCertificate :
    CanonicalPrimeIndexedProducerSpineCertificate where
  root_object_count := SaturationMonoid.coreMathematicalObject18_card
  root_goldbach_rh_path := SaturationMonoid.goldbachRHPrescribedPathCertificate
  canonical_support := PrimeIndexedSupport.canonical
  canonical_initial := PrimeIndexedSupport.canonical_initial
  no_binary_prime_support := no_injective_primeExponent_to_fin_two
  no_binary_supported_shadow := no_binary_coding_of_primeIndexedSupport
  no_binary_structured_bridge := no_binary_coding_of_structuredBridge
  no_binary_structured_front_door := no_binary_coding_of_structuredFrontDoor

end AffineRelaxation
end SaturationMonoid
