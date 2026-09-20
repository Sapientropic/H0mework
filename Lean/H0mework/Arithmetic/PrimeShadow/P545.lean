import H0mework.Arithmetic.PrimeProjection.P544

/-!
# Proposition 545: the coded descent shadow is exactly the exponent spine

P543 introduced a coded quotient to avoid the collapse of the free descent
quotient from P542.  P544 then proved that the code-compatible domain is the
maximal pullback-lift domain for that coded producer.

This file removes one remaining bit of slack: the coded quotient is not an
opaque extra carrier.  It is canonically equivalent to the preserved exponent
spine `ℕ`.  Therefore the same producer can be read through a direct
`ℕ`-valued shadow:

* arithmetic shadow = sigma iteration exponent;
* spectral shadow = the supplied spectral exponent code;
* pullback membership = code compatibility.

Boundary: this still does not manufacture the spectral exponent code from the
Euler/physics side.  It proves that once such a code is supplied, the common
mathematical shadow is forced to be the exponent spine, not a new arbitrary
quotient.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## The coded quotient is the exponent spine -/

/-- The canonical inverse from exponents back into the coded descent quotient. -/
def exponentToCodedDescentShadow (n : ℕ) : CodedDescentPrimeShadow :=
  Quot.mk CodedDescentShadowRel (Sum.inl n)

/-- THEOREM 1: the coded descent shadow is canonically equivalent to `ℕ`.

The nontrivial direction is the spectral/tagged atom: it is glued to the
arithmetic atom with the same exponent, so the quotient has no hidden degrees
of freedom beyond the exponent label. -/
def codedDescentPrimeShadowEquivNat : CodedDescentPrimeShadow ≃ ℕ where
  toFun := codedDescentShadowExponent
  invFun := exponentToCodedDescentShadow
  left_inv := by
    intro z
    refine Quot.inductionOn z ?_
    intro a
    cases a with
    | inl n =>
        rfl
    | inr tagged =>
        rcases tagged with ⟨n, s⟩
        exact Quot.sound (CodedDescentShadowRel.glue n s)
  right_inv := by
    intro n
    rfl

/-- THEOREM 2: the arithmetic face of the coded quotient reads exactly as the
sigma exponent. -/
theorem codedDescentPrimeShadowEquivNat_arithmetic
    (r : HalfSigmaArithmeticImage) :
    codedDescentPrimeShadowEquivNat (codedDescentArithmeticShadow r) =
      SigmaExponentImage.exponent r :=
  codedDescentShadowExponent_arithmetic r

/-- THEOREM 3: the spectral face of the coded quotient reads exactly as the
adapter's exponent code. -/
theorem codedDescentPrimeShadowEquivNat_spectral
    (A : SpectralExponentCodeAdapter)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    codedDescentPrimeShadowEquivNat (codedDescentSpectralShadow A s) =
      A.code s :=
  codedDescentShadowExponent_spectral A s

/-! ## The direct exponent-shadow producer -/

/-- The same Euler pullback producer, read directly through the canonical
exponent spine `ℕ`. -/
def exponentShadowEulerPrimeCouplingProducer
    (A : SpectralExponentCodeAdapter) :
    EulerPrimeCouplingProducers where
  PrimeShadow := ℕ
  arithmeticShadow := fun r => SigmaExponentImage.exponent r
  spectralShadow := A.code
  seed := eulerProductCouplingSeedCertificate

/-- A shadow isomorphism between two Euler prime producers: the common shadow
types are equivalent and both projection maps commute with that equivalence. -/
structure EulerPrimeProducerShadowEquiv
    (P Q : EulerPrimeCouplingProducers) where
  equiv : P.PrimeShadow ≃ Q.PrimeShadow
  arithmetic_commutes :
    ∀ r : HalfSigmaArithmeticImage,
      equiv (P.arithmeticShadow r) = Q.arithmeticShadow r
  spectral_commutes :
    ∀ s : H1SpectralProjection (1 / 2 : ℝ),
      equiv (P.spectralShadow s) = Q.spectralShadow s

/-- THEOREM 4: the coded descent producer is shadow-isomorphic to the direct
exponent-shadow producer. -/
def codedDescentProducer_shadowEquiv_exponentProducer
    (A : SpectralExponentCodeAdapter) :
    EulerPrimeProducerShadowEquiv
      (codedDescentEulerPrimeCouplingProducer A)
      (exponentShadowEulerPrimeCouplingProducer A) where
  equiv := codedDescentPrimeShadowEquivNat
  arithmetic_commutes := codedDescentPrimeShadowEquivNat_arithmetic
  spectral_commutes := codedDescentPrimeShadowEquivNat_spectral A

/-! ## Pullback membership for the direct exponent producer -/

/-- Pullback-liftability for the direct `ℕ`-shadow producer. -/
def ExponentShadowLiftable
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) : Prop :=
  ∃ z : (exponentShadowEulerPrimeCouplingProducer A).Carrier,
    EulerPrimeCouplingProducers.Carrier.arithmetic z = x.arithmetic ∧
      EulerPrimeCouplingProducers.Carrier.spectral z = x.spectral

/-- THEOREM 5: for the direct exponent-shadow producer, pullback membership is
again exactly code compatibility. -/
theorem exponentShadowLiftable_iff_allowed
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) :
    ExponentShadowLiftable A x ↔ CodedDescentAllowed A x := by
  constructor
  · intro hlift
    exact
      (EulerPrimeCouplingProducers.Carrier.mk_shadow_agreement_iff
        (P := exponentShadowEulerPrimeCouplingProducer A)
        x.arithmetic x.spectral).mp hlift
  · intro hallowed
    exact
      (EulerPrimeCouplingProducers.Carrier.mk_shadow_agreement_iff
        (P := exponentShadowEulerPrimeCouplingProducer A)
        x.arithmetic x.spectral).mpr hallowed

/-- THEOREM 6: every coded-domain point lifts into the direct exponent-shadow
pullback carrier. -/
def exponentShadowRestrictedLift
    (A : SpectralExponentCodeAdapter) :
    CodedAdmissibleDomain A ->
      (exponentShadowEulerPrimeCouplingProducer A).Carrier :=
  fun x =>
    ⟨(x.1.arithmetic, x.1.spectral), x.2⟩

/-- THEOREM 7: the direct exponent-shadow restricted lift preserves the
arithmetic projection. -/
theorem exponentShadowRestrictedLift_arithmetic
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    EulerPrimeCouplingProducers.Carrier.arithmetic
        (exponentShadowRestrictedLift A x) =
      x.1.arithmetic :=
  rfl

/-- THEOREM 8: the direct exponent-shadow restricted lift preserves the
spectral projection. -/
theorem exponentShadowRestrictedLift_spectral
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    EulerPrimeCouplingProducers.Carrier.spectral
        (exponentShadowRestrictedLift A x) =
      x.1.spectral :=
  rfl

/-! ## Completeness through the direct exponent spine -/

/-- Completeness on the direct exponent spine. -/
def exponentShadowCommonComplete (n : ℕ) : Prop :=
  HasPrimeAdditiveDecomposition n

/-- THEOREM 9: direct exponent-shadow completeness pulls back to image-level
Goldbach on the arithmetic side. -/
theorem exponentShadowCommonComplete_arithmetic
    (A : SpectralExponentCodeAdapter)
    (r : HalfSigmaArithmeticImage) :
    exponentShadowCommonComplete
        ((exponentShadowEulerPrimeCouplingProducer A).arithmeticShadow r) ↔
      HalfSigmaImageGoldbachComplete r := by
  change HasPrimeAdditiveDecomposition (SigmaExponentImage.exponent r) ↔
    HalfSigmaImageGoldbachComplete r
  exact (halfSigmaImageGoldbachComplete_iff_exponentGoldbach r).symm

/-- THEOREM 10: for any adapter, direct exponent-shadow completeness pulls
back to H¹ no-obstruction on the spectral side by the adapter law. -/
theorem exponentShadowCommonComplete_spectral
    (A : SpectralExponentCodeAdapter)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    exponentShadowCommonComplete
        ((exponentShadowEulerPrimeCouplingProducer A).spectralShadow s) ↔
      H1SpectralNoObstructionComplete s :=
  A.spectral_complete_iff s

/-- THEOREM 11: on the maximal coded domain, the direct exponent-shadow lift's
arithmetic completeness is exactly image-level Goldbach. -/
theorem exponentShadowRestricted_lift_common_iff_goldbach
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    exponentShadowCommonComplete
        ((exponentShadowEulerPrimeCouplingProducer A).arithmeticShadow
          (EulerPrimeCouplingProducers.Carrier.arithmetic
            (exponentShadowRestrictedLift A x))) ↔
      HalfSigmaImageGoldbachComplete x.1.arithmetic := by
  rw [exponentShadowRestrictedLift_arithmetic]
  change HasPrimeAdditiveDecomposition
      (SigmaExponentImage.exponent x.1.arithmetic) ↔
    HalfSigmaImageGoldbachComplete x.1.arithmetic
  exact
    (halfSigmaImageGoldbachComplete_iff_exponentGoldbach
      x.1.arithmetic).symm

/-- THEOREM 12: on the maximal coded domain, the direct exponent-shadow lift's
spectral completeness is exactly H¹ no-obstruction. -/
theorem exponentShadowRestricted_lift_common_iff_h1
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    exponentShadowCommonComplete
        ((exponentShadowEulerPrimeCouplingProducer A).spectralShadow
          (EulerPrimeCouplingProducers.Carrier.spectral
            (exponentShadowRestrictedLift A x))) ↔
      H1SpectralNoObstructionComplete x.1.spectral := by
  rw [exponentShadowRestrictedLift_spectral]
  exact exponentShadowCommonComplete_spectral A x.1.spectral

/-! ## Packaged exponent-spine normal form -/

/-- Compact certificate that the coded quotient has no extra mathematical
content beyond the exponent spine and that the direct exponent-shadow producer
has the same maximal-domain front door. -/
structure CodedDescentExponentSpineCertificate where
  shadow_equiv_nat : CodedDescentPrimeShadow ≃ ℕ
  producer :
    SpectralExponentCodeAdapter -> EulerPrimeCouplingProducers
  coded_to_exponent_shadow_equiv :
    ∀ A : SpectralExponentCodeAdapter,
      EulerPrimeProducerShadowEquiv
        (codedDescentEulerPrimeCouplingProducer A)
        (producer A)
  liftable :
    SpectralExponentCodeAdapter ->
      ArithmeticAdmissibleSevenFacet -> Prop
  liftable_iff_allowed :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : ArithmeticAdmissibleSevenFacet),
      liftable A x ↔ CodedDescentAllowed A x
  restricted_lift :
    ∀ A : SpectralExponentCodeAdapter,
      CodedAdmissibleDomain A ->
        (exponentShadowEulerPrimeCouplingProducer A).Carrier
  restricted_goldbach :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : CodedAdmissibleDomain A),
      exponentShadowCommonComplete
          ((exponentShadowEulerPrimeCouplingProducer A).arithmeticShadow
            (EulerPrimeCouplingProducers.Carrier.arithmetic
              (restricted_lift A x))) ↔
        HalfSigmaImageGoldbachComplete x.1.arithmetic
  restricted_h1 :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : CodedAdmissibleDomain A),
      exponentShadowCommonComplete
          ((exponentShadowEulerPrimeCouplingProducer A).spectralShadow
            (EulerPrimeCouplingProducers.Carrier.spectral
              (restricted_lift A x))) ↔
        H1SpectralNoObstructionComplete x.1.spectral

/-- THEOREM 13: the coded descent exponent-spine normal form certificate. -/
def codedDescentExponentSpineCertificate :
    CodedDescentExponentSpineCertificate where
  shadow_equiv_nat := codedDescentPrimeShadowEquivNat
  producer := exponentShadowEulerPrimeCouplingProducer
  coded_to_exponent_shadow_equiv :=
    codedDescentProducer_shadowEquiv_exponentProducer
  liftable := ExponentShadowLiftable
  liftable_iff_allowed := exponentShadowLiftable_iff_allowed
  restricted_lift := exponentShadowRestrictedLift
  restricted_goldbach := exponentShadowRestricted_lift_common_iff_goldbach
  restricted_h1 := exponentShadowRestricted_lift_common_iff_h1

end AffineRelaxation
end SaturationMonoid
