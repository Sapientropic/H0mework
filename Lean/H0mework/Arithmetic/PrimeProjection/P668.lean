import H0mework.Arithmetic.PrimeShadow.P667
import H0mework.Arithmetic.PrimeShadow.P518

/-!
# Proposition 668: even-coverage is the exact Goldbach/H1 producer boundary

P667 attaches the concrete coded-descent prime-shadow producer to the central
pressure root.  The remaining mathematical holy-grail debt is not another
tautological adapter.  P517/P518 already rule out the truth-value shortcut:
the producer has to carry prime-indexed structure.

This file sharpens the remaining debt into an exact boundary.  For any
support-indexed prime-shadow producer, if its supported coded domain covers
every even half-sigma arithmetic exponent, then ordinary even Goldbach is
equivalent to H¹ no-obstruction on that covered even domain.  Conversely,
coverage plus H¹ no-obstruction on the covered domain gives ordinary even
Goldbach.

Boundary: this still does not construct the final Euler/RH spectral support.
It proves the exact shape of the missing producer: the remaining object must
be an even-exponent coverage certificate for a non-tautological prime-indexed
shadow, not a result-shaped compatibility field.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Even half-sigma coverage -/

/-- The named half-sigma arithmetic point at even exponent `2 * n`. -/
def evenHalfSigmaArithmeticPoint (n : ℕ) : HalfSigmaArithmeticImage :=
  SigmaExponentImage.ofNat (1 / 2 : ℝ) (2 * n)

/-- THEOREM 1: image-level completeness at the named even half-sigma point is
ordinary additive-prime decomposition of `2 * n`. -/
theorem halfSigmaImageGoldbachComplete_evenPoint_iff
    (n : ℕ) :
    HalfSigmaImageGoldbachComplete (evenHalfSigmaArithmeticPoint n) ↔
      HasPrimeAdditiveDecomposition (2 * n) := by
  have h :=
    halfSigmaImageGoldbachComplete_iff_exponentGoldbach
      (evenHalfSigmaArithmeticPoint n)
  have hexp :
      SigmaExponentImage.exponent (evenHalfSigmaArithmeticPoint n) =
        2 * n :=
    SigmaExponentImage.exponent_ofNat_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 (2 * n)
  rw [hexp] at h
  exact h

/-- The even part of the supported coded domain of a prime-shadow producer. -/
def PrimeShadowEvenSupportedDomain
    (B : SupportIndexedPrimeShadowProducer) : Type :=
  { x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer //
      ∃ n : ℕ, 2 ≤ n ∧ x.1.arithmetic = evenHalfSigmaArithmeticPoint n }

/-- A support-indexed prime-shadow producer covers the ordinary Goldbach
domain when every even exponent `2 * n`, `n >= 2`, has a supported coded lift.
-/
def PrimeShadowEvenArithmeticCoverage
    (B : SupportIndexedPrimeShadowProducer) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer,
      x.1.arithmetic = evenHalfSigmaArithmeticPoint n

/-- H¹ no-obstruction on the even covered part of a prime-shadow producer. -/
def PrimeShadowCoveredEvenH1NoObstruction
    (B : SupportIndexedPrimeShadowProducer) : Prop :=
  ∀ (x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer)
    (n : ℕ), 2 ≤ n ->
      x.1.arithmetic = evenHalfSigmaArithmeticPoint n ->
        H1SpectralNoObstructionComplete x.1.spectral

/-! ## Exact boundary theorem -/

/-- THEOREM 2: once a non-tautological prime-shadow producer covers every
even half-sigma arithmetic exponent, ordinary even Goldbach is exactly H¹
no-obstruction on the covered even spectral domain.

This is an exact producer boundary, not a proof of Goldbach: the hard missing
input is the coverage certificate. -/
theorem evenGoldbach_iff_coveredEvenH1_of_primeShadowCoverage
    (B : SupportIndexedPrimeShadowProducer)
    (hcoverage : PrimeShadowEvenArithmeticCoverage B) :
    EvenGoldbachStatement ↔ PrimeShadowCoveredEvenH1NoObstruction B := by
  constructor
  · intro hgold x n hn harith
    have hsync :=
      SupportIndexedPrimeShadowProducer.supported_imageGoldbach_iff_h1
        B x
    apply hsync.mp
    rw [harith]
    exact (halfSigmaImageGoldbachComplete_evenPoint_iff n).mpr
      (hgold n hn)
  · intro hh1 n hn
    rcases hcoverage n hn with ⟨x, harith⟩
    have hsync :=
      SupportIndexedPrimeShadowProducer.supported_imageGoldbach_iff_h1
        B x
    have himage : HalfSigmaImageGoldbachComplete x.1.arithmetic :=
      hsync.mpr (hh1 x n hn harith)
    have hnamed : HalfSigmaImageGoldbachComplete
        (evenHalfSigmaArithmeticPoint n) := by
      rw [← harith]
      exact himage
    exact (halfSigmaImageGoldbachComplete_evenPoint_iff n).mp hnamed

/-! ## Coded-descent specialization -/

/-- Coded-descent even coverage for a concrete spectral exponent adapter. -/
def CodedDescentEvenArithmeticCoverage
    (A : SpectralExponentCodeAdapter) : Prop :=
  PrimeShadowEvenArithmeticCoverage (codedDescentSupportIndexedPrimeShadowProducer A)

/-- H¹ no-obstruction on the even covered part of the coded-descent producer. -/
def CodedDescentCoveredEvenH1NoObstruction
    (A : SpectralExponentCodeAdapter) : Prop :=
  PrimeShadowCoveredEvenH1NoObstruction
    (codedDescentSupportIndexedPrimeShadowProducer A)

/-- THEOREM 3: the exact even-coverage boundary specialized to P625's
canonical coded-descent producer. -/
theorem evenGoldbach_iff_codedDescentCoveredEvenH1_of_coverage
    (A : SpectralExponentCodeAdapter)
    (hcoverage : CodedDescentEvenArithmeticCoverage A) :
    EvenGoldbachStatement ↔
      CodedDescentCoveredEvenH1NoObstruction A :=
  evenGoldbach_iff_coveredEvenH1_of_primeShadowCoverage
    (codedDescentSupportIndexedPrimeShadowProducer A) hcoverage

/-! ## Packaged boundary certificate -/

/-- The exact remaining boundary for the Goldbach/H¹ producer.

The certificate keeps the anti-tautology gate from P518 together with the new
coverage equivalence: a final producer must be prime-indexed and must cover the
even half-sigma arithmetic domain. -/
structure PrimeShadowEvenCoverageBoundaryCertificate where
  truth_value_shadow_not_structured :
    Not
      (Nonempty
        (StructuredConcreteAdmissiblePrimeShadowBridge
          truthValuePrimeShadowProducer))
  no_total_math_front_door :
    Not (Nonempty FullDomainSpectralExponentCodeAdapter)
  even_coverage_iff :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenArithmeticCoverage B ->
        (EvenGoldbachStatement ↔
          PrimeShadowCoveredEvenH1NoObstruction B)
  coded_descent_even_coverage_iff :
    ∀ A : SpectralExponentCodeAdapter,
      CodedDescentEvenArithmeticCoverage A ->
        (EvenGoldbachStatement ↔
          CodedDescentCoveredEvenH1NoObstruction A)

/-- THEOREM 4: the canonical exact boundary certificate. -/
theorem primeShadowEvenCoverageBoundaryCertificate :
    PrimeShadowEvenCoverageBoundaryCertificate where
  truth_value_shadow_not_structured :=
    truthValuePrimeShadowProducer_not_structuredBridge
  no_total_math_front_door := no_fullDomainSpectralExponentCodeAdapter
  even_coverage_iff :=
    evenGoldbach_iff_coveredEvenH1_of_primeShadowCoverage
  coded_descent_even_coverage_iff :=
    evenGoldbach_iff_codedDescentCoveredEvenH1_of_coverage

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The P667 pressure root plus the exact even-coverage boundary for the
remaining mathematical holy-grail producer. -/
structure EvenCoverageHolyGrailBoundaryUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  coded_descent_pressure_root :
    CodedDescentPrimeShadowProducerPressureUnifiedRootCertificate E
  even_coverage_boundary :
    PrimeShadowEvenCoverageBoundaryCertificate
  coded_descent_even_coverage_iff :
    ∀ A : SpectralExponentCodeAdapter,
      CodedDescentEvenArithmeticCoverage A ->
        (EvenGoldbachStatement ↔
          CodedDescentCoveredEvenH1NoObstruction A)
  truth_value_shadow_not_structured :
    Not
      (Nonempty
        (StructuredConcreteAdmissiblePrimeShadowBridge
          truthValuePrimeShadowProducer))
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 5: the current central pressure root with the exact
even-coverage holy-grail boundary attached. -/
def evenCoverageHolyGrailBoundaryUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    EvenCoverageHolyGrailBoundaryUnifiedRootCertificate E where
  coded_descent_pressure_root :=
    codedDescentPrimeShadowProducerPressureUnifiedRootCertificate (E := E)
  even_coverage_boundary :=
    primeShadowEvenCoverageBoundaryCertificate
  coded_descent_even_coverage_iff :=
    evenGoldbach_iff_codedDescentCoveredEvenH1_of_coverage
  truth_value_shadow_not_structured :=
    truthValuePrimeShadowProducer_not_structuredBridge
  alpha_s_residual :=
    codedDescentPressure_alpha_s_residual (E := E)

/-- THEOREM 6: at the unified root, coded-descent even coverage is exactly the
remaining bridge between ordinary even Goldbach and covered H¹ no-obstruction.
-/
theorem evenCoverageRoot_codedDescent_evenGoldbach_iff
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (A : SpectralExponentCodeAdapter)
    (hcoverage : CodedDescentEvenArithmeticCoverage A) :
    EvenGoldbachStatement ↔
      CodedDescentCoveredEvenH1NoObstruction A :=
  (evenCoverageHolyGrailBoundaryUnifiedRootCertificate
    (E := E)).coded_descent_even_coverage_iff A hcoverage

end GrandUnification
end SaturationMonoid
