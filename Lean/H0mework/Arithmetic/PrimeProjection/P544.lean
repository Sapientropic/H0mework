import H0mework.Arithmetic.PrimeShadow.P543

/-!
# Proposition 544: the coded domain is the maximal pullback-lift domain

P543 replaced the too-coarse free descent quotient by a coded descent quotient.
This file proves that the code-compatibility predicate is not an arbitrary
side condition: it is exactly the condition for an admissible seven-facet state
to lift into the coded Euler pullback carrier.

Consequences:

* `CodedDescentAllowed A x` is equivalent to pullback membership;
* any other domain whose states lift into the coded producer is a subdomain of
  `CodedDescentAllowed A`;
* on this maximal restricted domain, half-sigma Goldbach and H¹
  no-obstruction synchronize through the coded common predicate.

Boundary: the spectral-code adapter still has to be produced from the intended
Euler/physics spectral data.  P544 proves the maximality of the domain once
such an adapter is supplied.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-- Pullback-liftability of an arithmetic-admissible state for the coded
descent producer. -/
def CodedDescentLiftable
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) : Prop :=
  ∃ z : (codedDescentEulerPrimeCouplingProducer A).Carrier,
    EulerPrimeCouplingProducers.Carrier.arithmetic z = x.arithmetic ∧
      EulerPrimeCouplingProducers.Carrier.spectral z = x.spectral

/-- THEOREM 1: for the coded producer, pullback-liftability is exactly
code-compatibility. -/
theorem codedDescentLiftable_iff_allowed
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) :
    CodedDescentLiftable A x ↔ CodedDescentAllowed A x := by
  constructor
  · intro hlift
    have hshadow :
        codedDescentArithmeticShadow x.arithmetic =
          codedDescentSpectralShadow A x.spectral :=
      (EulerPrimeCouplingProducers.Carrier.mk_shadow_agreement_iff
        (P := codedDescentEulerPrimeCouplingProducer A)
        x.arithmetic x.spectral).mp hlift
    have hcode := congrArg codedDescentShadowExponent hshadow
    rw [codedDescentShadowExponent_arithmetic,
      codedDescentShadowExponent_spectral] at hcode
    exact hcode
  · intro hallowed
    exact
      (EulerPrimeCouplingProducers.Carrier.mk_shadow_agreement_iff
        (P := codedDescentEulerPrimeCouplingProducer A)
        x.arithmetic x.spectral).mpr
          (codedDescent_shadow_eq_of_allowed A x hallowed)

/-- The domain of all coded-liftable admissible states. -/
def CodedDescentLiftableDomain
    (A : SpectralExponentCodeAdapter) : Type :=
  { x : ArithmeticAdmissibleSevenFacet // CodedDescentLiftable A x }

/-- THEOREM 2: the declared coded domain is equivalent to the full pullback
liftable domain. -/
def codedAdmissibleDomainEquivLiftableDomain
    (A : SpectralExponentCodeAdapter) :
    CodedAdmissibleDomain A ≃ CodedDescentLiftableDomain A where
  toFun x := ⟨x.1, (codedDescentLiftable_iff_allowed A x.1).mpr x.2⟩
  invFun x := ⟨x.1, (codedDescentLiftable_iff_allowed A x.1).mp x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- THEOREM 3: any admissible subdomain whose states lift into the coded
producer is contained in the coded domain. -/
theorem codedDescentAllowed_maximal
    (A : SpectralExponentCodeAdapter)
    (D : ArithmeticAdmissibleSevenFacet -> Prop)
    (hlift : ∀ x : ArithmeticAdmissibleSevenFacet,
      D x -> CodedDescentLiftable A x) :
    ∀ x : ArithmeticAdmissibleSevenFacet,
      D x -> CodedDescentAllowed A x := by
  intro x hx
  exact (codedDescentLiftable_iff_allowed A x).mp (hlift x hx)

/-- THEOREM 4: any strict enlargement of the coded domain contains a state
that cannot lift into the coded pullback carrier. -/
theorem codedDescentStrictEnlargement_has_unliftable
    (A : SpectralExponentCodeAdapter)
    (D : ArithmeticAdmissibleSevenFacet -> Prop)
    (_hcontains : ∀ x : ArithmeticAdmissibleSevenFacet,
      CodedDescentAllowed A x -> D x)
    (hstrict : ∃ x : ArithmeticAdmissibleSevenFacet,
      D x ∧ Not (CodedDescentAllowed A x)) :
    ∃ x : ArithmeticAdmissibleSevenFacet,
      D x ∧ Not (CodedDescentLiftable A x) := by
  rcases hstrict with ⟨x, hxD, hxNotAllowed⟩
  refine ⟨x, hxD, ?_⟩
  intro hlift
  exact hxNotAllowed ((codedDescentLiftable_iff_allowed A x).mp hlift)

/-! ## Restricted-domain synchronization -/

/-- THEOREM 5: on the maximal coded domain, image-level Goldbach is exactly
H¹ no-obstruction. -/
theorem codedRestricted_goldbach_iff_h1
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
      H1SpectralNoObstructionComplete x.1.spectral := by
  have hgold :
      HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
        HasPrimeAdditiveDecomposition
          (SigmaExponentImage.exponent x.1.arithmetic) :=
    halfSigmaImageGoldbachComplete_iff_exponentGoldbach x.1.arithmetic
  have hcode :
      HasPrimeAdditiveDecomposition
          (SigmaExponentImage.exponent x.1.arithmetic) ↔
        HasPrimeAdditiveDecomposition (A.code x.1.spectral) := by
    rw [x.2]
  exact hgold.trans (hcode.trans (A.spectral_complete_iff x.1.spectral))

/-- THEOREM 6: the same restricted synchronization read on the original real
rate coordinate. -/
theorem codedRestricted_rateGoldbach_iff_h1
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    HalfSigmaRateGoldbachComplete x.1.val.rate ↔
      H1SpectralNoObstructionComplete x.1.spectral := by
  have hrateImage := halfSigmaRateGoldbachComplete_of_image x.1.arithmetic
  have hrate : (x.1.arithmetic).1 = x.1.val.rate :=
    ArithmeticAdmissibleSevenFacet.arithmetic_rate_eq x.1
  have hrate' :
      HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        HalfSigmaImageGoldbachComplete x.1.arithmetic := by
    rw [← hrate]
    exact hrateImage
  exact hrate'.trans (codedRestricted_goldbach_iff_h1 A x)

/-- THEOREM 7: the restricted lift's carrier completeness is exactly
image-level Goldbach. -/
theorem codedRestricted_lift_common_iff_goldbach
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    codedDescentCommonComplete
        ((codedDescentEulerPrimeCouplingProducer A).arithmeticShadow
          (EulerPrimeCouplingProducers.Carrier.arithmetic
            (codedDescentRestrictedLift A x))) ↔
      HalfSigmaImageGoldbachComplete x.1.arithmetic := by
  rw [codedDescentRestrictedLift_arithmetic]
  exact codedDescentCommonComplete_arithmetic x.1.arithmetic

/-- THEOREM 8: the restricted lift's carrier completeness is exactly H¹
no-obstruction on the spectral side. -/
theorem codedRestricted_lift_common_iff_h1
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    codedDescentCommonComplete
        ((codedDescentEulerPrimeCouplingProducer A).spectralShadow
          (EulerPrimeCouplingProducers.Carrier.spectral
            (codedDescentRestrictedLift A x))) ↔
      H1SpectralNoObstructionComplete x.1.spectral := by
  rw [codedDescentRestrictedLift_spectral]
  exact codedDescentCommonComplete_spectral A x.1.spectral

/-! ## Packaged maximal-domain certificate -/

/-- Compact certificate that the coded descent domain is exactly the maximal
pullback-liftable domain and that the restricted bridge synchronizes the two
concrete completeness predicates. -/
structure CodedDescentMaximalDomainCertificate where
  liftable :
    SpectralExponentCodeAdapter ->
      ArithmeticAdmissibleSevenFacet -> Prop
  liftable_iff_allowed :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : ArithmeticAdmissibleSevenFacet),
      liftable A x ↔ CodedDescentAllowed A x
  allowed_equiv_liftable_domain :
    ∀ A : SpectralExponentCodeAdapter,
      CodedAdmissibleDomain A ≃ CodedDescentLiftableDomain A
  maximal :
    ∀ (A : SpectralExponentCodeAdapter)
      (D : ArithmeticAdmissibleSevenFacet -> Prop),
      (∀ x : ArithmeticAdmissibleSevenFacet, D x -> liftable A x) ->
        ∀ x : ArithmeticAdmissibleSevenFacet,
          D x -> CodedDescentAllowed A x
  strict_enlargement_has_unliftable :
    ∀ (A : SpectralExponentCodeAdapter)
      (D : ArithmeticAdmissibleSevenFacet -> Prop),
      (∀ x : ArithmeticAdmissibleSevenFacet,
        CodedDescentAllowed A x -> D x) ->
      (∃ x : ArithmeticAdmissibleSevenFacet,
        D x ∧ Not (CodedDescentAllowed A x)) ->
        ∃ x : ArithmeticAdmissibleSevenFacet,
          D x ∧ Not (liftable A x)
  restricted_goldbach_iff_h1 :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : CodedAdmissibleDomain A),
      HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
        H1SpectralNoObstructionComplete x.1.spectral
  restricted_rateGoldbach_iff_h1 :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : CodedAdmissibleDomain A),
      HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        H1SpectralNoObstructionComplete x.1.spectral

/-- THEOREM 9: the coded descent maximal-domain certificate. -/
def codedDescentMaximalDomainCertificate :
    CodedDescentMaximalDomainCertificate where
  liftable := CodedDescentLiftable
  liftable_iff_allowed := codedDescentLiftable_iff_allowed
  allowed_equiv_liftable_domain :=
    codedAdmissibleDomainEquivLiftableDomain
  maximal := codedDescentAllowed_maximal
  strict_enlargement_has_unliftable :=
    codedDescentStrictEnlargement_has_unliftable
  restricted_goldbach_iff_h1 := codedRestricted_goldbach_iff_h1
  restricted_rateGoldbach_iff_h1 := codedRestricted_rateGoldbach_iff_h1

end AffineRelaxation
end SaturationMonoid
