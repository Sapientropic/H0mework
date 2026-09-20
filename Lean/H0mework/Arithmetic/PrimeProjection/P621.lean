import H0mework.Arithmetic.PrimeShadow.P546
import H0mework.Realization.Relations.P620

/-!
# Proposition 621: supported coded mathematical front door

P620 gives a single finite/projection root for the unified equation, but its
mathematical holy-grail boundary still points at the older P516/P325 style
prime-shadow input.  P542-P546 sharpened that input:

* the free descent quotient collapses distinct prime codes;
* coded descent preserves the exponent spine;
* the coded domain is the maximal pullback-lift domain;
* the coded quotient is canonically `ℕ`;
* the honest spectral exponent producer is support-indexed, not silently total.

This file connects that corrected mathematical front door back to the P620
unified core.  It also proves the support-indexed synchronization theorem
directly: on the supported coded domain, half-sigma Goldbach completeness is
equivalent to H¹ no-obstruction without totalizing the spectral code.

Boundary: this still does not produce the physical/Euler support itself, and
it does not prove Goldbach or RH.  It removes the wrong full-domain front door
and records the precise supported/coded domain on which a future producer must
work.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Support-indexed synchronization -/

/-- THEOREM 1: on the support-indexed coded domain, image-level half-sigma
Goldbach is exactly H¹ no-obstruction.

This is the support-aware analogue of P544's restricted theorem.  It does not
require a total spectral code; it uses only the support witness carried by the
domain point. -/
theorem supportedRestricted_imageGoldbach_iff_h1
    (B : SupportedSpectralExponentCodeProducer)
    (x : SupportedCodedAdmissibleDomain B) :
    HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
      H1SpectralNoObstructionComplete x.1.spectral := by
  rcases x.2 with ⟨hs, hcode⟩
  have hgold :
      HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
        HasPrimeAdditiveDecomposition
          (SigmaExponentImage.exponent x.1.arithmetic) :=
    halfSigmaImageGoldbachComplete_iff_exponentGoldbach x.1.arithmetic
  have hcodeIff :
      HasPrimeAdditiveDecomposition
          (SigmaExponentImage.exponent x.1.arithmetic) ↔
        HasPrimeAdditiveDecomposition (B.code x.1.spectral hs) := by
    rw [hcode]
  exact hgold.trans
    (hcodeIff.trans (B.spectral_complete_iff x.1.spectral hs))

/-- THEOREM 2: the same supported synchronization read on the original
real-rate coordinate. -/
theorem supportedRestricted_rateGoldbach_iff_h1
    (B : SupportedSpectralExponentCodeProducer)
    (x : SupportedCodedAdmissibleDomain B) :
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
  exact hrate'.trans (supportedRestricted_imageGoldbach_iff_h1 B x)

/-! ## Prime-indexed support for the direct exponent spine -/

/-- The direct exponent spine carries prime indices faithfully. -/
theorem primeExponent_val_injective :
    Function.Injective (fun p : PrimeExponent => p.1) := by
  intro p q h
  exact Subtype.ext h

/-! ## Corrected mathematical front-door certificate -/

/-- Compact certificate for the corrected mathematical holy-grail front door.

The important content is negative and positive:

* free descent and full-domain coding are too broad;
* coded/support-indexed descent gives the maximal domain where the arithmetic
  and H¹ projections can be synchronized by a producer.
-/
structure SupportedCodedMathFrontDoorCertificate where
  free_descent_collapse :
    FreeDescentPrimeCollapseCertificate
  coded_prime_spine :
    CodedDescentPrimeSpineCertificate
  coded_maximal_domain :
    CodedDescentMaximalDomainCertificate
  exponent_spine :
    CodedDescentExponentSpineCertificate
  support_front_door :
    SupportedSpectralExponentFrontDoorCertificate
  no_full_domain_adapter :
    Not (Nonempty FullDomainSpectralExponentCodeAdapter)
  prime_exponent_code_injective :
    Function.Injective (fun p : PrimeExponent => p.1)
  supported_image_goldbach_iff_h1 :
    ∀ (B : SupportedSpectralExponentCodeProducer)
      (x : SupportedCodedAdmissibleDomain B),
      HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
        H1SpectralNoObstructionComplete x.1.spectral
  supported_rate_goldbach_iff_h1 :
    ∀ (B : SupportedSpectralExponentCodeProducer)
      (x : SupportedCodedAdmissibleDomain B),
      HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        H1SpectralNoObstructionComplete x.1.spectral

/-- THEOREM 3: the supported coded mathematical front-door certificate. -/
def supportedCodedMathFrontDoorCertificate :
    SupportedCodedMathFrontDoorCertificate where
  free_descent_collapse := freeDescentPrimeCollapseCertificate
  coded_prime_spine := codedDescentPrimeSpineCertificate
  coded_maximal_domain := codedDescentMaximalDomainCertificate
  exponent_spine := codedDescentExponentSpineCertificate
  support_front_door := supportedSpectralExponentFrontDoorCertificate
  no_full_domain_adapter := no_fullDomainSpectralExponentCodeAdapter
  prime_exponent_code_injective := primeExponent_val_injective
  supported_image_goldbach_iff_h1 :=
    supportedRestricted_imageGoldbach_iff_h1
  supported_rate_goldbach_iff_h1 :=
    supportedRestricted_rateGoldbach_iff_h1

end AffineRelaxation

/-! ## Connection back to the P620 unified core -/

/-- The current unified-equation finite core together with the corrected
support-indexed mathematical front door. -/
structure CurrentUnifiedEquationSupportedMathCoreCertificate where
  unified_finite_core :
    CurrentUnifiedEquationFiniteCoreCertificate
  supported_math_front_door :
    AffineRelaxation.SupportedCodedMathFrontDoorCertificate
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  supported_math_sync :
    ∀ (B : AffineRelaxation.SupportedSpectralExponentCodeProducer)
      (x : AffineRelaxation.SupportedCodedAdmissibleDomain B),
      AffineRelaxation.HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        AffineRelaxation.H1SpectralNoObstructionComplete x.1.spectral
  no_total_math_front_door :
    Not (Nonempty AffineRelaxation.FullDomainSpectralExponentCodeAdapter)

/-- THEOREM 4: the current unified core with corrected supported mathematical
front door is inhabited. -/
def currentUnifiedEquationSupportedMathCoreCertificate :
    CurrentUnifiedEquationSupportedMathCoreCertificate where
  unified_finite_core := currentUnifiedEquationFiniteCoreCertificate
  supported_math_front_door :=
    AffineRelaxation.supportedCodedMathFrontDoorCertificate
  alpha_s_residual :=
    CurrentUnifiedEquationFiniteCoreCertificate.alpha_s_residual
      currentUnifiedEquationFiniteCoreCertificate
  supported_math_sync :=
    AffineRelaxation.supportedRestricted_rateGoldbach_iff_h1
  no_total_math_front_door :=
    AffineRelaxation.no_fullDomainSpectralExponentCodeAdapter

end SaturationMonoid
