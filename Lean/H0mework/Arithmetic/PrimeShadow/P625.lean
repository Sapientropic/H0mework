import H0mework.Arithmetic.PrimeShadow.P624

/-!
# Proposition 625: coded descent supplies the injective liftability producer

P624 proved the exact domain theorem for any support-indexed prime-shadow
producer, conditional on injectivity of its arithmetic shadow.  This file
discharges that condition for the canonical coded-descent producer from P543.

The key point is small but load-bearing: the coded quotient remembers the
arithmetic exponent.  Therefore two arithmetic shadows can be equal only when
their chosen half-sigma exponents are equal, and the half-sigma exponent image
is faithful on `0 < σ < 1`.

Boundary: this still does not build the final Euler/RH support.  It proves
that once a spectral exponent adapter is supplied, the canonical coded descent
front door is already a genuine P324 pullback-liftability domain, not merely a
result-shaped synchronization predicate.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## The coded arithmetic shadow is injective -/

/-- THEOREM 1: the canonical coded-descent arithmetic shadow is injective.

The coded quotient carries a canonical exponent projection, and the
half-sigma image is exactly the image of `ofNat`.  Equality of shadows
therefore reflects equality of exponents and hence equality of image points.
-/
theorem codedDescentArithmeticShadow_injective :
    Function.Injective codedDescentArithmeticShadow := by
  intro r s h
  have hexp :
      SigmaExponentImage.exponent r = SigmaExponentImage.exponent s := by
    have h' := congrArg codedDescentShadowExponent h
    simpa [codedDescentShadowExponent_arithmetic] using h'
  calc
    r =
        SigmaExponentImage.ofNat (1 / 2 : ℝ)
          (SigmaExponentImage.exponent r) := by
      exact (SigmaExponentImage.ofNat_exponent_eq r).symm
    _ =
        SigmaExponentImage.ofNat (1 / 2 : ℝ)
          (SigmaExponentImage.exponent s) := by
      rw [hexp]
    _ = s := SigmaExponentImage.ofNat_exponent_eq s

/-! ## Canonical support-indexed producer from a coded adapter -/

/-- THEOREM 2: every spectral exponent adapter induces a support-indexed
prime-shadow producer with full support.  This is not a total front door over
unrestricted arithmetic states; the supported/coded domain still enforces
code agreement pointwise. -/
def codedDescentSupportIndexedPrimeShadowProducer
    (A : SpectralExponentCodeAdapter) :
    SupportIndexedPrimeShadowProducer where
  producer := codedDescentEulerPrimeCouplingProducer A
  support := fun _ => True
  code := fun s _ => A.code s
  supported_shadow_code := by
    intro s _hs
    dsimp [codedDescentEulerPrimeCouplingProducer, codedDescentSpectralShadow,
      codedDescentArithmeticShadow]
    rw [SigmaExponentImage.exponent_ofNat_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2]
    exact (Quot.sound (CodedDescentShadowRel.glue (A.code s) s)).symm
  commonComplete := codedDescentCommonComplete
  common_arithmetic := codedDescentCommonComplete_arithmetic
  common_spectral := by
    intro s _hs
    exact codedDescentCommonComplete_spectral A s

/-- THEOREM 3: the canonical coded support producer inherits arithmetic-shadow
injectivity. -/
theorem codedDescentSupportIndexedPrimeShadowProducer_arithmeticShadow_injective
    (A : SpectralExponentCodeAdapter) :
    Function.Injective
      (codedDescentSupportIndexedPrimeShadowProducer A).producer.arithmeticShadow :=
  codedDescentArithmeticShadow_injective

/-- THEOREM 4: the supported-coded predicate induced by the canonical support
producer is exactly the older P543 `CodedDescentAllowed` predicate. -/
theorem codedDescentSupportedAllowed_iff_codedDescentAllowed
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) :
    SupportedCodedDescentAllowed
        ((codedDescentSupportIndexedPrimeShadowProducer A)
          |>.toCommonPredicateProducer
          |>.toSupportedSpectralExponentCodeProducer)
        x ↔
      CodedDescentAllowed A x := by
  constructor
  · rintro ⟨_hs, hcode⟩
    change SigmaExponentImage.exponent x.arithmetic = A.code x.spectral
    exact hcode
  · intro hcode
    exact ⟨trivial, hcode⟩

/-- THEOREM 5: for the canonical coded-descent producer, code compatibility is
equivalent to supported P324 pullback liftability.  This is P624's conditional
iff with the injectivity condition discharged. -/
theorem codedDescentAllowed_iff_primeShadowSupportedLiftable
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) :
    CodedDescentAllowed A x ↔
      PrimeShadowSupportedLiftable
        (codedDescentSupportIndexedPrimeShadowProducer A) x := by
  rw [← codedDescentSupportedAllowed_iff_codedDescentAllowed A x]
  exact
    supportedCodedAllowed_iff_primeShadowSupportedLiftable_of_arithmeticShadow_injective
      (codedDescentSupportIndexedPrimeShadowProducer A)
      (codedDescentSupportIndexedPrimeShadowProducer_arithmeticShadow_injective A)
      x

/-- THEOREM 6: the canonical coded domain is equivalent to the supported
pullback-liftable subtype. -/
def codedDescentDomainEquivPrimeShadowLiftableDomain
    (A : SpectralExponentCodeAdapter) :
    CodedAdmissibleDomain A ≃
      { x : ArithmeticAdmissibleSevenFacet //
          PrimeShadowSupportedLiftable
            (codedDescentSupportIndexedPrimeShadowProducer A) x } where
  toFun x :=
    ⟨x.1,
      (codedDescentAllowed_iff_primeShadowSupportedLiftable A x.1).mp x.2⟩
  invFun x :=
    ⟨x.1,
      (codedDescentAllowed_iff_primeShadowSupportedLiftable A x.1).mpr x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-! ## Packaged canonical liftability certificate -/

/-- Compact certificate that the canonical coded descent front door has the
P624 liftability equivalence without any additional injectivity hypothesis. -/
structure CodedDescentPrimeShadowLiftabilityCertificate where
  to_support_indexed :
    SpectralExponentCodeAdapter -> SupportIndexedPrimeShadowProducer
  arithmeticShadow_injective :
    Function.Injective codedDescentArithmeticShadow
  allowed_iff_liftable :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : ArithmeticAdmissibleSevenFacet),
      CodedDescentAllowed A x ↔
        PrimeShadowSupportedLiftable (to_support_indexed A) x
  domain_equiv :
    ∀ A : SpectralExponentCodeAdapter,
      CodedAdmissibleDomain A ≃
        { x : ArithmeticAdmissibleSevenFacet //
            PrimeShadowSupportedLiftable (to_support_indexed A) x }

/-- THEOREM 7: the canonical coded-descent liftability certificate. -/
def codedDescentPrimeShadowLiftabilityCertificate :
    CodedDescentPrimeShadowLiftabilityCertificate where
  to_support_indexed := codedDescentSupportIndexedPrimeShadowProducer
  arithmeticShadow_injective := codedDescentArithmeticShadow_injective
  allowed_iff_liftable := codedDescentAllowed_iff_primeShadowSupportedLiftable
  domain_equiv := codedDescentDomainEquivPrimeShadowLiftableDomain

end AffineRelaxation

/-! ## Connection back to the current unified-equation root -/

/-- The current unified-equation root with the P624 injectivity condition
discharged for the canonical coded-descent producer. -/
structure CurrentUnifiedEquationCodedDescentLiftabilityCoreCertificate where
  prime_shadow_liftability_core :
    CurrentUnifiedEquationPrimeShadowLiftabilityCoreCertificate
  coded_descent_liftability :
    AffineRelaxation.CodedDescentPrimeShadowLiftabilityCertificate
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 8: the current unified root with canonical coded-descent
pullback-liftability welded in unconditionally. -/
def currentUnifiedEquationCodedDescentLiftabilityCoreCertificate :
    CurrentUnifiedEquationCodedDescentLiftabilityCoreCertificate where
  prime_shadow_liftability_core :=
    currentUnifiedEquationPrimeShadowLiftabilityCoreCertificate
  coded_descent_liftability :=
    AffineRelaxation.codedDescentPrimeShadowLiftabilityCertificate
  alpha_s_residual :=
    CurrentUnifiedEquationPrimeShadowLiftabilityCoreCertificate.alpha_s_residual
      currentUnifiedEquationPrimeShadowLiftabilityCoreCertificate

end SaturationMonoid
