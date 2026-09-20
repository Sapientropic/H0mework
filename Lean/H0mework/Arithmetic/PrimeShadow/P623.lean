import H0mework.Arithmetic.PrimeProjection.P622

/-!
# Proposition 623: prime-shadow support producer front door

P622 lowers the mathematical front door from a result-shaped spectral
compatibility field to a common predicate on the exponent spine.  This file
lowers it one step further, back to the P324 Euler-coupled pullback carrier.

The producer obligation is now prime-shadow shaped:

* provide an `EulerPrimeCouplingProducers` object;
* provide supported spectral points and their exponent code;
* prove supported spectral shadows agree with the arithmetic shadow of that
  exponent;
* provide a common predicate on the producer's `PrimeShadow`;
* prove arithmetic and supported spectral pullbacks of that predicate.

Lean then reconstructs the P622 common-predicate producer, hence the P621
support-indexed spectral producer and the restricted Goldbach/H¹
synchronization theorem.

Boundary: this still does not construct the actual Euler-product/RH physics
support.  It prevents the next producer from living merely on `ℕ`; it must pass
through a prime-indexed Euler pullback shadow.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Prime-shadow support producer -/

/-- A support-indexed producer whose common predicate lives on the P324
Euler-coupled prime-shadow object, not directly on the target theorem. -/
structure SupportIndexedPrimeShadowProducer where
  producer : EulerPrimeCouplingProducers
  support : H1SpectralProjection (1 / 2 : ℝ) -> Prop
  code :
    ∀ s : H1SpectralProjection (1 / 2 : ℝ),
      support s -> ℕ
  supported_shadow_code :
    ∀ (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : support s),
      producer.spectralShadow s =
        producer.arithmeticShadow
          (SigmaExponentImage.ofNat (1 / 2 : ℝ) (code s hs))
  commonComplete : producer.PrimeShadow -> Prop
  common_arithmetic :
    ∀ r : HalfSigmaArithmeticImage,
      commonComplete (producer.arithmeticShadow r) ↔
        HalfSigmaImageGoldbachComplete r
  common_spectral :
    ∀ (s : H1SpectralProjection (1 / 2 : ℝ)) (_hs : support s),
      commonComplete (producer.spectralShadow s) ↔
        H1SpectralNoObstructionComplete s

namespace SupportIndexedPrimeShadowProducer

/-- The arithmetic half-sigma point named by a natural exponent. -/
def arithmeticPointOfCode (_B : SupportIndexedPrimeShadowProducer)
    (n : ℕ) : HalfSigmaArithmeticImage :=
  SigmaExponentImage.ofNat (1 / 2 : ℝ) n

/-- THEOREM 1: the prime-shadow producer induces the P622
common-predicate-on-exponents producer. -/
def toCommonPredicateProducer
    (B : SupportIndexedPrimeShadowProducer) :
    SupportIndexedCommonPredicateProducer where
  support := B.support
  code := B.code
  commonComplete := fun n =>
    B.commonComplete
      (B.producer.arithmeticShadow (B.arithmeticPointOfCode n))
  common_arithmetic := by
    intro n
    have harith :
        B.commonComplete
            (B.producer.arithmeticShadow (B.arithmeticPointOfCode n)) ↔
          HalfSigmaImageGoldbachComplete (B.arithmeticPointOfCode n) :=
      B.common_arithmetic (B.arithmeticPointOfCode n)
    have hgold :
        HalfSigmaImageGoldbachComplete (B.arithmeticPointOfCode n) ↔
          HasPrimeAdditiveDecomposition n := by
      have h :
          HalfSigmaImageGoldbachComplete (B.arithmeticPointOfCode n) ↔
            HasPrimeAdditiveDecomposition
              (SigmaExponentImage.exponent (B.arithmeticPointOfCode n)) :=
        halfSigmaImageGoldbachComplete_iff_exponentGoldbach
          (B.arithmeticPointOfCode n)
      have hexp :
          SigmaExponentImage.exponent (B.arithmeticPointOfCode n) = n :=
        SigmaExponentImage.exponent_ofNat_of_mem_Ioo
          halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 n
      exact h.trans (by rw [hexp])
    exact harith.trans hgold
  common_spectral := by
    intro s hs
    have hshadow := B.supported_shadow_code s hs
    have hspectral :
        B.commonComplete (B.producer.spectralShadow s) ↔
          H1SpectralNoObstructionComplete s :=
      B.common_spectral s hs
    change
      B.commonComplete
          (B.producer.arithmeticShadow
            (SigmaExponentImage.ofNat (1 / 2 : ℝ) (B.code s hs))) ↔
        H1SpectralNoObstructionComplete s
    rw [← hshadow]
    exact hspectral

/-- THEOREM 2: the induced producer has the same spectral support. -/
theorem toCommon_support
    (B : SupportIndexedPrimeShadowProducer)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    (B.toCommonPredicateProducer).support s = B.support s :=
  rfl

/-- THEOREM 3: the induced producer has the same supported code. -/
theorem toCommon_code
    (B : SupportIndexedPrimeShadowProducer)
    (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : B.support s) :
    (B.toCommonPredicateProducer).code s hs = B.code s hs :=
  rfl

/-- THEOREM 4: P622's support-indexed synchronization follows from the
prime-shadow pullback producer. -/
theorem supported_rateGoldbach_iff_h1
    (B : SupportIndexedPrimeShadowProducer)
    (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer) :
    HalfSigmaRateGoldbachComplete x.1.val.rate ↔
      H1SpectralNoObstructionComplete x.1.spectral :=
  commonPredicate_supported_rateGoldbach_iff_h1
    B.toCommonPredicateProducer x

/-- THEOREM 5: the same synchronization on the image-level arithmetic
projection. -/
theorem supported_imageGoldbach_iff_h1
    (B : SupportIndexedPrimeShadowProducer)
    (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer) :
    HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
      H1SpectralNoObstructionComplete x.1.spectral :=
  commonPredicate_supported_imageGoldbach_iff_h1
    B.toCommonPredicateProducer x

end SupportIndexedPrimeShadowProducer

/-! ## Packaged prime-shadow front door -/

/-- Certificate that the corrected mathematical front door can be fed by a
support-indexed Euler prime-shadow producer. -/
structure PrimeShadowSupportedMathFrontDoorCertificate where
  p622_front_door :
    CommonPredicateSupportedMathFrontDoorCertificate
  to_common_predicate :
    SupportIndexedPrimeShadowProducer ->
      SupportIndexedCommonPredicateProducer
  to_supported_code_producer :
    SupportIndexedPrimeShadowProducer ->
      SupportedSpectralExponentCodeProducer
  supported_rate_sync_from_prime_shadow :
    ∀ (B : SupportIndexedPrimeShadowProducer)
      (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer),
      HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        H1SpectralNoObstructionComplete x.1.spectral
  supported_image_sync_from_prime_shadow :
    ∀ (B : SupportIndexedPrimeShadowProducer)
      (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer),
      HalfSigmaImageGoldbachComplete x.1.arithmetic ↔
        H1SpectralNoObstructionComplete x.1.spectral
  no_total_math_front_door :
    Not (Nonempty FullDomainSpectralExponentCodeAdapter)

/-- THEOREM 6: the prime-shadow supported mathematical front door. -/
def primeShadowSupportedMathFrontDoorCertificate :
    PrimeShadowSupportedMathFrontDoorCertificate where
  p622_front_door := commonPredicateSupportedMathFrontDoorCertificate
  to_common_predicate :=
    SupportIndexedPrimeShadowProducer.toCommonPredicateProducer
  to_supported_code_producer := fun B =>
    (SupportIndexedPrimeShadowProducer.toCommonPredicateProducer B)
      |>.toSupportedSpectralExponentCodeProducer
  supported_rate_sync_from_prime_shadow :=
    SupportIndexedPrimeShadowProducer.supported_rateGoldbach_iff_h1
  supported_image_sync_from_prime_shadow :=
    SupportIndexedPrimeShadowProducer.supported_imageGoldbach_iff_h1
  no_total_math_front_door := no_fullDomainSpectralExponentCodeAdapter

end AffineRelaxation

/-! ## Connection back to the current unified-equation root -/

/-- The current unified-equation root with the mathematical front door lowered
all the way to support-indexed Euler prime-shadow pullback data. -/
structure CurrentUnifiedEquationPrimeShadowMathCoreCertificate where
  common_predicate_math_core :
    CurrentUnifiedEquationCommonPredicateMathCoreCertificate
  prime_shadow_front_door :
    AffineRelaxation.PrimeShadowSupportedMathFrontDoorCertificate
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  prime_shadow_sync :
    ∀ (B : AffineRelaxation.SupportIndexedPrimeShadowProducer)
      (x : AffineRelaxation.CommonPredicateSupportedCodedDomain
        B.toCommonPredicateProducer),
      AffineRelaxation.HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        AffineRelaxation.H1SpectralNoObstructionComplete x.1.spectral

/-- THEOREM 7: the current unified core can be read through a support-indexed
Euler prime-shadow producer front door. -/
def currentUnifiedEquationPrimeShadowMathCoreCertificate :
    CurrentUnifiedEquationPrimeShadowMathCoreCertificate where
  common_predicate_math_core :=
    currentUnifiedEquationCommonPredicateMathCoreCertificate
  prime_shadow_front_door :=
    AffineRelaxation.primeShadowSupportedMathFrontDoorCertificate
  alpha_s_residual :=
    CurrentUnifiedEquationCommonPredicateMathCoreCertificate.alpha_s_residual
      currentUnifiedEquationCommonPredicateMathCoreCertificate
  prime_shadow_sync :=
    AffineRelaxation.SupportIndexedPrimeShadowProducer.supported_rateGoldbach_iff_h1

end SaturationMonoid
