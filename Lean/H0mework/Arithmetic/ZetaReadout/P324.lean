import H0mework.Realization.RelaxationAlgebra.P323

/-!
# Proposition 324: the Euler-coupled pullback carrier

P321 ruled out the unconstrained product carrier.  P322 supplied the honest
Euler-product seed: the arithmetic half-sigma atomic support and the analytic
Euler product share a prime-indexed producer.  P323 then ruled out the tempting
shortcut that `sigma = 1/2` collapses addition and multiplication.

This leaves a precise next carrier shape: not a free product, and not a
self-duality quotient, but a pullback/fiber product over a common
prime-indexed shadow.

This file proves that shape abstractly.  Given a producer of a common
`PrimeShadow` for the arithmetic and H1-spectral projections, the coupled
carrier is exactly the pullback

`{(a,s) | arithmeticShadow a = spectralShadow s}`.

It has the expected universal property: any other system with arithmetic and
spectral projections satisfying the same shadow equality factors uniquely
through it.  Any completeness predicate on the common shadow then pulls back
faithfully to both projections on the coupled carrier.

Boundary: this is the canonical carrier/certificate shape for the next step.
It does not provide the concrete prime-shadow producer that would prove
Goldbach, RH, or an equivalence between them.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Producer interface -/

/-- Data needed to replace the rejected product carrier by an Euler-coupled
pullback carrier.  The field `seed` records P322's prime-indexed Euler product
certificate; the two shadow maps are the remaining producer work.

The shadow type is intentionally abstract.  A future concrete theorem must
instantiate it with the right prime-indexed/descent object, not merely with an
arbitrary product coordinate.
-/
structure EulerPrimeCouplingProducers where
  PrimeShadow : Type
  arithmeticShadow : HalfSigmaArithmeticImage -> PrimeShadow
  spectralShadow : H1SpectralProjection (1 / 2 : ℝ) -> PrimeShadow
  seed : EulerProductCouplingSeedCertificate

namespace EulerPrimeCouplingProducers

/-! ## The pullback carrier -/

/-- The Euler-coupled Goldbach/H1 carrier: pairs whose arithmetic and spectral
prime shadows agree. -/
def Carrier (P : EulerPrimeCouplingProducers) : Type :=
  { z : HalfSigmaArithmeticImage × H1SpectralProjection (1 / 2 : ℝ) //
      P.arithmeticShadow z.1 = P.spectralShadow z.2 }

namespace Carrier

/-- Arithmetic projection of the coupled carrier. -/
def arithmetic {P : EulerPrimeCouplingProducers} (x : P.Carrier) :
    HalfSigmaArithmeticImage :=
  x.1.1

/-- H1-spectral projection of the coupled carrier. -/
def spectral {P : EulerPrimeCouplingProducers} (x : P.Carrier) :
    H1SpectralProjection (1 / 2 : ℝ) :=
  x.1.2

/-- THEOREM 1: on the coupled carrier, the two prime shadows agree by
construction. -/
theorem shadow_agreement {P : EulerPrimeCouplingProducers}
    (x : P.Carrier) :
    P.arithmeticShadow (arithmetic x) =
      P.spectralShadow (spectral x) :=
  x.2

/-- THEOREM 2: the two projections are jointly faithful. -/
theorem ext {P : EulerPrimeCouplingProducers}
    {x y : P.Carrier}
    (ha : arithmetic x = arithmetic y)
    (hs : spectral x = spectral y) :
    x = y := by
  apply Subtype.ext
  exact Prod.ext ha hs

/-- THEOREM 3: membership in the pullback carrier is exactly shadow equality.
-/
theorem mk_shadow_agreement_iff {P : EulerPrimeCouplingProducers}
    (a : HalfSigmaArithmeticImage)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    (∃ x : P.Carrier, arithmetic x = a ∧ spectral x = s) ↔
      P.arithmeticShadow a = P.spectralShadow s := by
  constructor
  · rintro ⟨x, ha, hs⟩
    calc
      P.arithmeticShadow a =
          P.arithmeticShadow (arithmetic x) := by rw [ha]
      _ = P.spectralShadow (spectral x) := shadow_agreement x
      _ = P.spectralShadow s := by rw [hs]
  · intro h
    exact ⟨⟨(a, s), h⟩, rfl, rfl⟩

/-- THEOREM 4: if the same arithmetic point is coupled to two spectral
points, their prime shadows must be equal.  This is the formal way the
pullback carrier blocks the P321-style free-product mismatch. -/
theorem same_arithmetic_forces_same_spectral_shadow
    {P : EulerPrimeCouplingProducers}
    {x y : P.Carrier}
    (ha : arithmetic x = arithmetic y) :
    P.spectralShadow (spectral x) =
      P.spectralShadow (spectral y) := by
  calc
    P.spectralShadow (spectral x) =
        P.arithmeticShadow (arithmetic x) := (shadow_agreement x).symm
    _ = P.arithmeticShadow (arithmetic y) := by rw [ha]
    _ = P.spectralShadow (spectral y) := shadow_agreement y

/-- Lift any system whose arithmetic and spectral projections have matching
prime shadows into the Euler-coupled pullback carrier. -/
def lift {P : EulerPrimeCouplingProducers} {X : Type}
    (a : X -> HalfSigmaArithmeticImage)
    (s : X -> H1SpectralProjection (1 / 2 : ℝ))
    (h : ∀ x : X, P.arithmeticShadow (a x) = P.spectralShadow (s x)) :
    X -> P.Carrier :=
  fun x => ⟨(a x, s x), h x⟩

/-- THEOREM 5: the lifted map has the requested arithmetic projection. -/
theorem lift_arithmetic {P : EulerPrimeCouplingProducers} {X : Type}
    (a : X -> HalfSigmaArithmeticImage)
    (s : X -> H1SpectralProjection (1 / 2 : ℝ))
    (h : ∀ x : X, P.arithmeticShadow (a x) = P.spectralShadow (s x))
    (x : X) :
    arithmetic (lift (P := P) a s h x) = a x :=
  rfl

/-- THEOREM 6: the lifted map has the requested spectral projection. -/
theorem lift_spectral {P : EulerPrimeCouplingProducers} {X : Type}
    (a : X -> HalfSigmaArithmeticImage)
    (s : X -> H1SpectralProjection (1 / 2 : ℝ))
    (h : ∀ x : X, P.arithmeticShadow (a x) = P.spectralShadow (s x))
    (x : X) :
    spectral (lift (P := P) a s h x) = s x :=
  rfl

/-- THEOREM 7: the lift is unique among maps with the same two projections.
This is the pullback universal property. -/
theorem lift_unique {P : EulerPrimeCouplingProducers} {X : Type}
    (a : X -> HalfSigmaArithmeticImage)
    (s : X -> H1SpectralProjection (1 / 2 : ℝ))
    (h : ∀ x : X, P.arithmeticShadow (a x) = P.spectralShadow (s x))
    (f : X -> P.Carrier)
    (ha : ∀ x : X, arithmetic (f x) = a x)
    (hs : ∀ x : X, spectral (f x) = s x) :
    f = lift (P := P) a s h := by
  funext x
  exact ext (ha x) (hs x)

/-! ## Faithful pullback of a common completeness predicate -/

/-- Global completeness on the coupled carrier induced by a predicate on the
common prime shadow. -/
def globalComplete {P : EulerPrimeCouplingProducers}
    (C : P.PrimeShadow -> Prop) (x : P.Carrier) : Prop :=
  C (P.arithmeticShadow (arithmetic x))

/-- Arithmetic completeness induced by the same common prime-shadow predicate.
-/
def arithmeticComplete {P : EulerPrimeCouplingProducers}
    (C : P.PrimeShadow -> Prop) (a : HalfSigmaArithmeticImage) : Prop :=
  C (P.arithmeticShadow a)

/-- Spectral completeness induced by the same common prime-shadow predicate.
-/
def spectralComplete {P : EulerPrimeCouplingProducers}
    (C : P.PrimeShadow -> Prop)
    (s : H1SpectralProjection (1 / 2 : ℝ)) : Prop :=
  C (P.spectralShadow s)

/-- THEOREM 8: arithmetic completeness is a faithful pullback of the global
coupled-carrier predicate. -/
theorem arithmetic_pullback {P : EulerPrimeCouplingProducers}
    (C : P.PrimeShadow -> Prop) (x : P.Carrier) :
    arithmeticComplete (P := P) C (arithmetic x) ↔
      globalComplete (P := P) C x :=
  Iff.rfl

/-- THEOREM 9: spectral completeness is a faithful pullback of the same global
coupled-carrier predicate. -/
theorem spectral_pullback {P : EulerPrimeCouplingProducers}
    (C : P.PrimeShadow -> Prop) (x : P.Carrier) :
    spectralComplete (P := P) C (spectral x) ↔
      globalComplete (P := P) C x := by
  unfold spectralComplete globalComplete
  rw [← shadow_agreement x]

/-- THEOREM 10: on the Euler-coupled carrier, the arithmetic and spectral
completeness predicates induced by the same prime-shadow predicate are
equivalent. -/
theorem arithmetic_iff_spectral {P : EulerPrimeCouplingProducers}
    (C : P.PrimeShadow -> Prop) (x : P.Carrier) :
    arithmeticComplete (P := P) C (arithmetic x) ↔
      spectralComplete (P := P) C (spectral x) := by
  exact (arithmetic_pullback C x).trans (spectral_pullback C x).symm

/-- Packaged certificate for the Euler-coupled pullback carrier. -/
structure PullbackCarrierCertificate (P : EulerPrimeCouplingProducers) where
  carrier : Type
  arithmeticProjection : carrier -> HalfSigmaArithmeticImage
  spectralProjection : carrier -> H1SpectralProjection (1 / 2 : ℝ)
  shadow_agreement :
    ∀ x : carrier,
      P.arithmeticShadow (arithmeticProjection x) =
        P.spectralShadow (spectralProjection x)
  projections_jointly_faithful :
    ∀ x y : carrier,
      arithmeticProjection x = arithmeticProjection y ->
        spectralProjection x = spectralProjection y -> x = y
  universal_lift :
    ∀ {X : Type}
      (a : X -> HalfSigmaArithmeticImage)
      (s : X -> H1SpectralProjection (1 / 2 : ℝ)),
      (∀ x : X, P.arithmeticShadow (a x) = P.spectralShadow (s x)) ->
        X -> carrier
  universal_lift_arithmetic :
    ∀ {X : Type}
      (a : X -> HalfSigmaArithmeticImage)
      (s : X -> H1SpectralProjection (1 / 2 : ℝ))
      (h : ∀ x : X, P.arithmeticShadow (a x) = P.spectralShadow (s x))
      (x : X),
      arithmeticProjection (universal_lift a s h x) = a x
  universal_lift_spectral :
    ∀ {X : Type}
      (a : X -> HalfSigmaArithmeticImage)
      (s : X -> H1SpectralProjection (1 / 2 : ℝ))
      (h : ∀ x : X, P.arithmeticShadow (a x) = P.spectralShadow (s x))
      (x : X),
      spectralProjection (universal_lift a s h x) = s x
  completeness_pullback :
    ∀ (C : P.PrimeShadow -> Prop) (x : carrier),
      C (P.arithmeticShadow (arithmeticProjection x)) ↔
        C (P.spectralShadow (spectralProjection x))

/-- THEOREM 11: the canonical pullback-carrier certificate generated from an
Euler prime coupling producer. -/
def pullbackCarrierCertificate (P : EulerPrimeCouplingProducers) :
    PullbackCarrierCertificate P where
  carrier := P.Carrier
  arithmeticProjection := arithmetic
  spectralProjection := spectral
  shadow_agreement := shadow_agreement
  projections_jointly_faithful := by
    intro x y ha hs
    exact ext ha hs
  universal_lift := by
    intro X a s h
    exact lift a s h
  universal_lift_arithmetic := by
    intro X a s h x
    exact lift_arithmetic a s h x
  universal_lift_spectral := by
    intro X a s h x
    exact lift_spectral a s h x
  completeness_pullback := by
    intro C x
    exact arithmetic_iff_spectral C x

end Carrier
end EulerPrimeCouplingProducers

end AffineRelaxation
end SaturationMonoid
