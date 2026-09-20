import H0mework.Arithmetic.PrimeProjection.P621

/-!
# Proposition 622: common-predicate support producer front door

P621 corrected the mathematical holy-grail front door: the spectral exponent
producer is support-indexed, not silently total.  One field of that producer,
however,

`HasPrimeAdditiveDecomposition (code s hs) ↔ H1SpectralNoObstructionComplete s`,

is still a result-shaped compatibility field.  This file lowers that field to
a smaller producer interface: a supported spectral code plus a common
predicate on the exponent spine whose two pullbacks are verified separately.

Thus a future Euler/physics producer does not get to write the Goldbach/H¹
synchronization theorem directly.  It must supply:

* the supported spectral code;
* a common exponent-side predicate;
* the arithmetic pullback of that predicate;
* the supported spectral pullback of that predicate.

From those four pieces Lean reconstructs the P621 support-indexed producer and
the restricted Goldbach/H¹ synchronization theorem.

Boundary: this still does not construct the actual Euler/physics support, and
it does not prove Goldbach or RH.  It removes one more result-shaped field from
the front door and replaces it with a pullback-shaped producer obligation.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Common-predicate support producer -/

/-- A stricter support-indexed spectral producer.

Instead of directly storing `HasPrimeAdditiveDecomposition code ↔ H¹`, it
stores a common predicate on the exponent spine and proves the arithmetic and
spectral pullbacks separately. -/
structure SupportIndexedCommonPredicateProducer where
  support : H1SpectralProjection (1 / 2 : ℝ) -> Prop
  code :
    ∀ s : H1SpectralProjection (1 / 2 : ℝ),
      support s -> ℕ
  commonComplete : ℕ -> Prop
  common_arithmetic :
    ∀ n : ℕ,
      commonComplete n ↔ HasPrimeAdditiveDecomposition n
  common_spectral :
    ∀ (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : support s),
      commonComplete (code s hs) ↔
        H1SpectralNoObstructionComplete s

namespace SupportIndexedCommonPredicateProducer

/-- THEOREM 1: the P621 result-shaped spectral compatibility is derived from
the two common-predicate pullbacks. -/
theorem spectral_complete_iff_from_common
    (B : SupportIndexedCommonPredicateProducer)
    (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : B.support s) :
    HasPrimeAdditiveDecomposition (B.code s hs) ↔
      H1SpectralNoObstructionComplete s :=
  (B.common_arithmetic (B.code s hs)).symm.trans
    (B.common_spectral s hs)

/-- A common-predicate producer induces the P621 support-indexed spectral
exponent code producer. -/
def toSupportedSpectralExponentCodeProducer
    (B : SupportIndexedCommonPredicateProducer) :
    SupportedSpectralExponentCodeProducer where
  support := B.support
  code := B.code
  spectral_complete_iff := spectral_complete_iff_from_common B

/-- THEOREM 2: support is unchanged by the lowering map. -/
theorem toSupported_support
    (B : SupportIndexedCommonPredicateProducer)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    (toSupportedSpectralExponentCodeProducer B).support s = B.support s :=
  rfl

/-- THEOREM 3: code is unchanged by the lowering map. -/
theorem toSupported_code
    (B : SupportIndexedCommonPredicateProducer)
    (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : B.support s) :
    (toSupportedSpectralExponentCodeProducer B).code s hs = B.code s hs :=
  rfl

end SupportIndexedCommonPredicateProducer

/-! ## Direct restricted synchronization from common pullbacks -/

/-- The supported coded domain induced by a common-predicate producer. -/
abbrev CommonPredicateSupportedCodedDomain
    (B : SupportIndexedCommonPredicateProducer) : Type :=
  SupportedCodedAdmissibleDomain
    (B.toSupportedSpectralExponentCodeProducer)

/-- THEOREM 4: on the support-indexed coded domain, image-level Goldbach and
H¹ no-obstruction synchronize by way of the common predicate, not by an
unstructured result field. -/
theorem commonPredicate_supported_imageGoldbach_iff_h1
    (B : SupportIndexedCommonPredicateProducer)
    (x : CommonPredicateSupportedCodedDomain B) :
    HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
      H1SpectralNoObstructionComplete x.1.spectral := by
  rcases x.2 with ⟨hs, hcode⟩
  change B.support x.1.spectral at hs
  change
    SigmaExponentImage.exponent x.1.arithmetic =
      B.code x.1.spectral hs at hcode
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
    (hcodeIff.trans
      (B.spectral_complete_iff_from_common x.1.spectral hs))

/-- THEOREM 5: the same common-predicate synchronization read on the raw rate
coordinate. -/
theorem commonPredicate_supported_rateGoldbach_iff_h1
    (B : SupportIndexedCommonPredicateProducer)
    (x : CommonPredicateSupportedCodedDomain B) :
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
  exact hrate'.trans
    (commonPredicate_supported_imageGoldbach_iff_h1 B x)

/-! ## Packaged lowered front door -/

/-- Certificate that P621's support-indexed mathematical front door can be
fed by the stricter common-predicate producer interface. -/
structure CommonPredicateSupportedMathFrontDoorCertificate where
  p621_front_door :
    SupportedCodedMathFrontDoorCertificate
  to_supported_producer :
    SupportIndexedCommonPredicateProducer ->
      SupportedSpectralExponentCodeProducer
  spectral_iff_from_common :
    ∀ (B : SupportIndexedCommonPredicateProducer)
      (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : B.support s),
      HasPrimeAdditiveDecomposition (B.code s hs) ↔
        H1SpectralNoObstructionComplete s
  supported_image_sync_from_common :
    ∀ (B : SupportIndexedCommonPredicateProducer)
      (x : CommonPredicateSupportedCodedDomain B),
      HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
        H1SpectralNoObstructionComplete x.1.spectral
  supported_rate_sync_from_common :
    ∀ (B : SupportIndexedCommonPredicateProducer)
      (x : CommonPredicateSupportedCodedDomain B),
      HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        H1SpectralNoObstructionComplete x.1.spectral
  no_total_math_front_door :
    Not (Nonempty FullDomainSpectralExponentCodeAdapter)

/-- THEOREM 6: the common-predicate supported mathematical front door. -/
def commonPredicateSupportedMathFrontDoorCertificate :
    CommonPredicateSupportedMathFrontDoorCertificate where
  p621_front_door := supportedCodedMathFrontDoorCertificate
  to_supported_producer :=
    SupportIndexedCommonPredicateProducer.toSupportedSpectralExponentCodeProducer
  spectral_iff_from_common :=
    SupportIndexedCommonPredicateProducer.spectral_complete_iff_from_common
  supported_image_sync_from_common :=
    commonPredicate_supported_imageGoldbach_iff_h1
  supported_rate_sync_from_common :=
    commonPredicate_supported_rateGoldbach_iff_h1
  no_total_math_front_door := no_fullDomainSpectralExponentCodeAdapter

end AffineRelaxation

/-! ## Connection back to the current unified-equation root -/

/-- The current unified-equation root with the mathematical front door lowered
from a support-indexed result field to common-predicate pullback data. -/
structure CurrentUnifiedEquationCommonPredicateMathCoreCertificate where
  supported_math_core :
    CurrentUnifiedEquationSupportedMathCoreCertificate
  lowered_common_predicate_front_door :
    AffineRelaxation.CommonPredicateSupportedMathFrontDoorCertificate
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  common_predicate_sync :
    ∀ (B : AffineRelaxation.SupportIndexedCommonPredicateProducer)
      (x : AffineRelaxation.CommonPredicateSupportedCodedDomain B),
      AffineRelaxation.HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        AffineRelaxation.H1SpectralNoObstructionComplete x.1.spectral

/-- THEOREM 7: the current unified core can be read through the lowered
common-predicate mathematical front door. -/
def currentUnifiedEquationCommonPredicateMathCoreCertificate :
    CurrentUnifiedEquationCommonPredicateMathCoreCertificate where
  supported_math_core := currentUnifiedEquationSupportedMathCoreCertificate
  lowered_common_predicate_front_door :=
    AffineRelaxation.commonPredicateSupportedMathFrontDoorCertificate
  alpha_s_residual :=
    CurrentUnifiedEquationSupportedMathCoreCertificate.alpha_s_residual
      currentUnifiedEquationSupportedMathCoreCertificate
  common_predicate_sync :=
    AffineRelaxation.commonPredicate_supported_rateGoldbach_iff_h1

end SaturationMonoid
