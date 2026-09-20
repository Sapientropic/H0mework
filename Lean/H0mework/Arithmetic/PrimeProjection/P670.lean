import H0mework.Arithmetic.PrimeProjection.P669

/-!
# Proposition 670: coded-descent even coverage is adapter even-code range

P669 lowers the P668 even-coverage boundary to support-code surjectivity for a
support-indexed prime-shadow producer.  For the canonical coded-descent
producer from P625, support is total and the supported code is exactly the
adapter field `A.code`.

This file therefore lowers the remaining coded-descent producer debt one more
layer: the missing object is not an opaque prime-shadow coverage certificate.
It is exactly an even-code range certificate for the spectral exponent adapter.

Boundary: this still does not construct the final Euler/RH spectral adapter.
It proves that, once such an adapter covers every even exponent, the P669
Goldbach/H¹ boundary applies on the stricter supported-liftable coded-descent
domain with no additional injectivity hypothesis; P625 already discharged that
injectivity for coded descent.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Adapter even-code range -/

/-- A spectral exponent adapter covers the ordinary even Goldbach exponents
when every `2 * n`, `n >= 2`, occurs as the code of some H¹ spectral point. -/
def SpectralExponentEvenCodeSurjective
    (A : SpectralExponentCodeAdapter) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ s : H1SpectralProjection (1 / 2 : ℝ), A.code s = 2 * n

/-- The P669 support-code surjectivity predicate specialized to the canonical
coded-descent producer. -/
def CodedDescentEvenSupportCodeSurjective
    (A : SpectralExponentCodeAdapter) : Prop :=
  PrimeShadowEvenSupportCodeSurjective
    (codedDescentSupportIndexedPrimeShadowProducer A)

/-- H¹ no-obstruction on actual supported-liftable even coded-descent points.
-/
def CodedDescentEvenLiftableH1NoObstruction
    (A : SpectralExponentCodeAdapter) : Prop :=
  PrimeShadowEvenLiftableH1NoObstruction
    (codedDescentSupportIndexedPrimeShadowProducer A)

/-- THEOREM 1: for coded descent, P669 support-code surjectivity is exactly
surjectivity of the adapter's own code map onto the even exponents. -/
theorem codedDescentEvenSupportCodeSurjective_iff_adapterEvenCodeSurjective
    (A : SpectralExponentCodeAdapter) :
    CodedDescentEvenSupportCodeSurjective A ↔
      SpectralExponentEvenCodeSurjective A := by
  constructor
  · intro hsurj n hn
    rcases hsurj n hn with ⟨s, _hs, hcode⟩
    refine ⟨s, ?_⟩
    simpa [codedDescentSupportIndexedPrimeShadowProducer] using hcode
  · intro hadapter n hn
    rcases hadapter n hn with ⟨s, hcode⟩
    refine ⟨s, trivial, ?_⟩
    simpa [codedDescentSupportIndexedPrimeShadowProducer] using hcode

/-- THEOREM 2: coded-descent P668 coverage is exactly the adapter even-code
range condition. -/
theorem codedDescentEvenArithmeticCoverage_iff_adapterEvenCodeSurjective
    (A : SpectralExponentCodeAdapter) :
    CodedDescentEvenArithmeticCoverage A ↔
      SpectralExponentEvenCodeSurjective A := by
  rw [CodedDescentEvenArithmeticCoverage,
    primeShadowEvenArithmeticCoverage_iff_evenSupportCodeSurjective]
  exact codedDescentEvenSupportCodeSurjective_iff_adapterEvenCodeSurjective A

/-- THEOREM 3: an adapter even-code range certificate is sufficient to read
ordinary even Goldbach as H¹ no-obstruction on the actual supported-liftable
coded-descent even domain. -/
theorem evenGoldbach_iff_codedDescentLiftableH1_of_adapterEvenCodeSurjective
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentEvenCodeSurjective A) :
    EvenGoldbachStatement ↔
      CodedDescentEvenLiftableH1NoObstruction A := by
  exact
    evenGoldbach_iff_evenLiftableH1_of_evenSupportCodeSurjective_and_injective
      (codedDescentSupportIndexedPrimeShadowProducer A)
      ((codedDescentEvenSupportCodeSurjective_iff_adapterEvenCodeSurjective A).mpr
        hrange)
      (codedDescentSupportIndexedPrimeShadowProducer_arithmeticShadow_injective A)

/-- THEOREM 4: the same coded-descent liftable-domain equivalence can be read
directly from P668 coded-descent coverage; P670 identifies that coverage with
adapter even-code range. -/
theorem evenGoldbach_iff_codedDescentLiftableH1_of_codedCoverage
    (A : SpectralExponentCodeAdapter)
    (hcoverage : CodedDescentEvenArithmeticCoverage A) :
    EvenGoldbachStatement ↔
      CodedDescentEvenLiftableH1NoObstruction A := by
  exact
    evenGoldbach_iff_evenLiftableH1_of_primeShadowCoverage_and_injective
      (codedDescentSupportIndexedPrimeShadowProducer A)
      hcoverage
      (codedDescentSupportIndexedPrimeShadowProducer_arithmeticShadow_injective A)

/-! ## Packaged adapter-range boundary -/

/-- The P670 boundary certificate: for the canonical coded-descent front door,
the remaining even producer obligation is exactly the even range of
`SpectralExponentCodeAdapter.code`. -/
structure CodedDescentAdapterEvenRangeBoundaryCertificate where
  p669_boundary :
    EvenSupportCodeSurjectivityBoundaryCertificate
  adapter_even_code_surjective :
    SpectralExponentCodeAdapter -> Prop
  adapter_range_iff_support_code :
    ∀ A : SpectralExponentCodeAdapter,
      CodedDescentEvenSupportCodeSurjective A ↔
        adapter_even_code_surjective A
  adapter_range_iff_coded_coverage :
    ∀ A : SpectralExponentCodeAdapter,
      CodedDescentEvenArithmeticCoverage A ↔
        adapter_even_code_surjective A
  adapter_range_iff_liftable_h1 :
    ∀ A : SpectralExponentCodeAdapter,
      adapter_even_code_surjective A ->
        (EvenGoldbachStatement ↔
          CodedDescentEvenLiftableH1NoObstruction A)
  coded_coverage_iff_liftable_h1 :
    ∀ A : SpectralExponentCodeAdapter,
      CodedDescentEvenArithmeticCoverage A ->
        (EvenGoldbachStatement ↔
          CodedDescentEvenLiftableH1NoObstruction A)

/-- DEFINITION 2: the canonical P670 adapter-range boundary. -/
def codedDescentAdapterEvenRangeBoundaryCertificate :
    CodedDescentAdapterEvenRangeBoundaryCertificate where
  p669_boundary := evenSupportCodeSurjectivityBoundaryCertificate
  adapter_even_code_surjective := SpectralExponentEvenCodeSurjective
  adapter_range_iff_support_code :=
    codedDescentEvenSupportCodeSurjective_iff_adapterEvenCodeSurjective
  adapter_range_iff_coded_coverage :=
    codedDescentEvenArithmeticCoverage_iff_adapterEvenCodeSurjective
  adapter_range_iff_liftable_h1 :=
    evenGoldbach_iff_codedDescentLiftableH1_of_adapterEvenCodeSurjective
  coded_coverage_iff_liftable_h1 :=
    evenGoldbach_iff_codedDescentLiftableH1_of_codedCoverage

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P670's coded-descent adapter range boundary
welded below the P669 support-code producer boundary. -/
structure CodedDescentAdapterRangeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p669_root :
    EvenSupportCodeProducerBoundaryUnifiedRootCertificate E
  adapter_range_boundary :
    CodedDescentAdapterEvenRangeBoundaryCertificate
  adapter_range_iff_support_code :
    ∀ A : SpectralExponentCodeAdapter,
      CodedDescentEvenSupportCodeSurjective A ↔
        SpectralExponentEvenCodeSurjective A
  adapter_range_iff_coded_coverage :
    ∀ A : SpectralExponentCodeAdapter,
      CodedDescentEvenArithmeticCoverage A ↔
        SpectralExponentEvenCodeSurjective A
  adapter_range_iff_liftable_h1 :
    ∀ A : SpectralExponentCodeAdapter,
      SpectralExponentEvenCodeSurjective A ->
        (EvenGoldbachStatement ↔
          CodedDescentEvenLiftableH1NoObstruction A)
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 5: the current central root with the P670 adapter-range boundary.
-/
def codedDescentAdapterRangeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CodedDescentAdapterRangeUnifiedRootCertificate E where
  p669_root := evenSupportCodeProducerBoundaryUnifiedRootCertificate (E := E)
  adapter_range_boundary := codedDescentAdapterEvenRangeBoundaryCertificate
  adapter_range_iff_support_code :=
    codedDescentEvenSupportCodeSurjective_iff_adapterEvenCodeSurjective
  adapter_range_iff_coded_coverage :=
    codedDescentEvenArithmeticCoverage_iff_adapterEvenCodeSurjective
  adapter_range_iff_liftable_h1 :=
    evenGoldbach_iff_codedDescentLiftableH1_of_adapterEvenCodeSurjective
  alpha_s_residual :=
    (evenSupportCodeProducerBoundaryUnifiedRootCertificate
      (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
