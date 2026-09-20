import H0mework.Arithmetic.PrimeProjection.P668

/-!
# Proposition 669: even coverage descends to support-code surjectivity

P668 pins the remaining Goldbach/H¹ producer debt to even half-sigma
arithmetic coverage.  This file lowers that coverage obligation by one more
layer.  A support-indexed prime-shadow producer does not have to directly
assert that the supported coded domain covers every even arithmetic point.
It is enough to provide, for every even exponent `2 * n`, a supported spectral
point whose code is exactly `2 * n`.

Lean then assembles the arithmetic-admissible seven-facet point by using the
P325 arithmetic embedding, proves it lies in the supported coded domain, and
recovers the P668 coverage theorem.

Boundary: this still does not construct the final Euler/RH spectral support.
It proves the exact producer interface just below P668: even support-code
surjectivity is sufficient for the P668 even-coverage boundary, without using
the truth-value shadow shortcut ruled out by P517/P518.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Arithmetic assembly at a supported spectral point -/

/-- THEOREM 2: assembling an admissible point from a spectral projection
round-trips back to that spectral projection. -/
theorem ofArithmetic_spectral_eq
    (facets : Fin 7 -> Prop)
    (s : H1SpectralProjection (1 / 2 : ℝ))
    (r : HalfSigmaArithmeticImage) :
    (ArithmeticAdmissibleSevenFacet.ofArithmetic
      facets s.phase s.analytic r).spectral = s := by
  cases s
  rfl

/-! ## Even support-code surjectivity -/

/-- A support-indexed prime-shadow producer is even-code-surjective when every
ordinary Goldbach exponent `2 * n`, `n >= 2`, is the supported code of some
spectral point. -/
def PrimeShadowEvenSupportCodeSurjective
    (B : SupportIndexedPrimeShadowProducer) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : B.support s),
      B.code s hs = 2 * n

/-- The canonical seven-facet point assembled from an even arithmetic point and
a supported spectral lift. -/
def evenCodeSurjectiveAssembledPoint
    (_B : SupportIndexedPrimeShadowProducer)
    (s : H1SpectralProjection (1 / 2 : ℝ))
    (n : ℕ) : ArithmeticAdmissibleSevenFacet :=
  ArithmeticAdmissibleSevenFacet.ofArithmetic
    (fun _ : Fin 7 => True) s.phase s.analytic
    (evenHalfSigmaArithmeticPoint n)

/-- THEOREM 3: if a spectral lift is supported and carries code `2 * n`, then
the assembled seven-facet point lies in the supported coded domain and has the
named even arithmetic projection. -/
theorem evenCodeSurjective_assembled_mem_domain
    (B : SupportIndexedPrimeShadowProducer)
    (n : ℕ)
    (s : H1SpectralProjection (1 / 2 : ℝ))
    (hs : B.support s)
    (hcode : B.code s hs = 2 * n) :
    ∃ x : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer,
      x.1.arithmetic = evenHalfSigmaArithmeticPoint n := by
  let x0 := evenCodeSurjectiveAssembledPoint B s n
  have harith : x0.arithmetic = evenHalfSigmaArithmeticPoint n :=
    ofArithmetic_arithmetic_eq
      (evenHalfSigmaArithmeticPoint n)
      (fun _ : Fin 7 => True) s.phase s.analytic
  have hspectral : x0.spectral = s :=
    ofArithmetic_spectral_eq
      (fun _ : Fin 7 => True) s
      (evenHalfSigmaArithmeticPoint n)
  have hsx : B.support x0.spectral := by
    rw [hspectral]
    exact hs
  have hcode_x :
      SigmaExponentImage.exponent x0.arithmetic =
        B.code x0.spectral hsx := by
    have hexp :
        SigmaExponentImage.exponent (evenHalfSigmaArithmeticPoint n) =
          2 * n :=
      SigmaExponentImage.exponent_ofNat_of_mem_Ioo
        halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 (2 * n)
    calc
      SigmaExponentImage.exponent x0.arithmetic =
          SigmaExponentImage.exponent (evenHalfSigmaArithmeticPoint n) := by
        rw [harith]
      _ = 2 * n := hexp
      _ = B.code x0.spectral hsx := by
        have hcode_spectral :
            B.code x0.spectral hsx = B.code s hs := by
          cases hspectral
          congr
        exact (hcode_spectral.trans hcode).symm
  refine ⟨⟨x0, ?_⟩, harith⟩
  refine ⟨hsx, ?_⟩
  change
    SigmaExponentImage.exponent x0.arithmetic =
      B.code x0.spectral hsx
  exact hcode_x

/-- THEOREM 4: even support-code surjectivity implies the P668 even arithmetic
coverage condition. -/
theorem primeShadowEvenArithmeticCoverage_of_evenSupportCodeSurjective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B) :
    PrimeShadowEvenArithmeticCoverage B := by
  intro n hn
  rcases hsurj n hn with ⟨s, hs, hcode⟩
  exact evenCodeSurjective_assembled_mem_domain B n s hs hcode

/-- THEOREM 5: the P668 coverage condition itself forces even support-code
surjectivity.  The supported coded-domain witness already contains a supported
spectral point and a code equality; the named even arithmetic point only
computes that code to `2 * n`. -/
theorem evenSupportCodeSurjective_of_primeShadowEvenArithmeticCoverage
    (B : SupportIndexedPrimeShadowProducer)
    (hcoverage : PrimeShadowEvenArithmeticCoverage B) :
    PrimeShadowEvenSupportCodeSurjective B := by
  intro n hn
  rcases hcoverage n hn with ⟨x, harith⟩
  rcases x.2 with ⟨hs, hcode⟩
  change B.support x.1.spectral at hs
  change
    SigmaExponentImage.exponent x.1.arithmetic =
      B.code x.1.spectral hs at hcode
  refine ⟨x.1.spectral, hs, ?_⟩
  have hexp :
      SigmaExponentImage.exponent (evenHalfSigmaArithmeticPoint n) =
        2 * n :=
    SigmaExponentImage.exponent_ofNat_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 (2 * n)
  calc
    B.code x.1.spectral hs =
        SigmaExponentImage.exponent x.1.arithmetic := hcode.symm
    _ = SigmaExponentImage.exponent (evenHalfSigmaArithmeticPoint n) := by
        rw [harith]
    _ = 2 * n := hexp

/-- THEOREM 6: P668 even coverage is exactly even support-code surjectivity.
This removes `coverage` as a separate opaque obligation: it is precisely the
claim that the producer's supported code range contains every even exponent. -/
theorem primeShadowEvenArithmeticCoverage_iff_evenSupportCodeSurjective
    (B : SupportIndexedPrimeShadowProducer) :
    PrimeShadowEvenArithmeticCoverage B ↔
      PrimeShadowEvenSupportCodeSurjective B := by
  constructor
  · exact evenSupportCodeSurjective_of_primeShadowEvenArithmeticCoverage B
  · exact primeShadowEvenArithmeticCoverage_of_evenSupportCodeSurjective B

/-- THEOREM 7: after lowering the producer obligation to even support-code
surjectivity, ordinary even Goldbach is still exactly covered H¹
no-obstruction. -/
theorem evenGoldbach_iff_coveredEvenH1_of_evenSupportCodeSurjective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B) :
    EvenGoldbachStatement ↔ PrimeShadowCoveredEvenH1NoObstruction B :=
  evenGoldbach_iff_coveredEvenH1_of_primeShadowCoverage B
    (primeShadowEvenArithmeticCoverage_of_evenSupportCodeSurjective B hsurj)

/-! ## Liftable even H¹ boundary -/

/-- H¹ no-obstruction on actual P624 supported-liftable even points. -/
def PrimeShadowEvenLiftableH1NoObstruction
    (B : SupportIndexedPrimeShadowProducer) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ x : { x : ArithmeticAdmissibleSevenFacet //
        PrimeShadowSupportedLiftable B x },
      x.1.arithmetic = evenHalfSigmaArithmeticPoint n ∧
        H1SpectralNoObstructionComplete x.1.spectral

/-- THEOREM 8: even support-code surjectivity plus ordinary even Goldbach
produces H¹ no-obstruction on actual supported-liftable Euler-pullback points.
-/
theorem evenLiftableH1_of_goldbach_and_evenSupportCodeSurjective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B)
    (hgold : EvenGoldbachStatement) :
    PrimeShadowEvenLiftableH1NoObstruction B := by
  intro n hn
  rcases hsurj n hn with ⟨s, hs, hcode⟩
  rcases evenCodeSurjective_assembled_mem_domain B n s hs hcode with
    ⟨x, harith⟩
  have hlift : PrimeShadowSupportedLiftable B x.1 :=
    commonPredicateSupportedCodedDomain_subset_primeShadowLiftable B x
  have hsync :=
    SupportIndexedPrimeShadowProducer.supported_imageGoldbach_iff_h1 B x
  have himage : HalfSigmaImageGoldbachComplete x.1.arithmetic := by
    rw [harith]
    exact (halfSigmaImageGoldbachComplete_evenPoint_iff n).mpr
      (hgold n hn)
  refine ⟨⟨x.1, hlift⟩, harith, ?_⟩
  exact hsync.mp himage

/-- THEOREM 9: with arithmetic-shadow injectivity, H¹ no-obstruction on the
even supported-liftable Euler-pullback domain recovers ordinary even Goldbach.

The injectivity assumption is exactly P624's price for turning supported
pullback liftability back into the supported coded domain. -/
theorem goldbach_of_evenLiftableH1_and_arithmeticShadow_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hinj : Function.Injective B.producer.arithmeticShadow)
    (hliftH1 : PrimeShadowEvenLiftableH1NoObstruction B) :
    EvenGoldbachStatement := by
  intro n hn
  rcases hliftH1 n hn with ⟨x, harith, hh1⟩
  have hallowed :
      SupportedCodedDescentAllowed
          (B.toCommonPredicateProducer.toSupportedSpectralExponentCodeProducer)
          x.1 :=
    (supportedCodedAllowed_iff_primeShadowSupportedLiftable_of_arithmeticShadow_injective
      B hinj x.1).mpr x.2
  let xd : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer :=
    ⟨x.1, hallowed⟩
  have hsync :=
    SupportIndexedPrimeShadowProducer.supported_imageGoldbach_iff_h1 B xd
  have himage : HalfSigmaImageGoldbachComplete xd.1.arithmetic :=
    hsync.mpr hh1
  have hnamed :
      HalfSigmaImageGoldbachComplete (evenHalfSigmaArithmeticPoint n) := by
    rw [← harith]
    exact himage
  exact (halfSigmaImageGoldbachComplete_evenPoint_iff n).mp hnamed

/-- THEOREM 10: the P668 Goldbach/H¹ equivalence can be read at the stricter
P624 supported-liftability layer, provided the producer supplies even
support-code surjectivity and arithmetic-shadow injectivity. -/
theorem evenGoldbach_iff_evenLiftableH1_of_evenSupportCodeSurjective_and_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B)
    (hinj : Function.Injective B.producer.arithmeticShadow) :
    EvenGoldbachStatement ↔
      PrimeShadowEvenLiftableH1NoObstruction B := by
  constructor
  · exact evenLiftableH1_of_goldbach_and_evenSupportCodeSurjective B hsurj
  · exact goldbach_of_evenLiftableH1_and_arithmeticShadow_injective B hinj

/-- THEOREM 11: the same stricter P624 liftable-domain equivalence can be read
directly from P668 even coverage, because coverage is exactly support-code
surjectivity. -/
theorem evenGoldbach_iff_evenLiftableH1_of_primeShadowCoverage_and_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hcoverage : PrimeShadowEvenArithmeticCoverage B)
    (hinj : Function.Injective B.producer.arithmeticShadow) :
    EvenGoldbachStatement ↔
      PrimeShadowEvenLiftableH1NoObstruction B :=
  evenGoldbach_iff_evenLiftableH1_of_evenSupportCodeSurjective_and_injective B
    ((primeShadowEvenArithmeticCoverage_iff_evenSupportCodeSurjective B).mp
      hcoverage)
    hinj

/-! ## Packaged support-code producer boundary -/

/-- The P669 boundary certificate: support-code surjectivity is the producer
interface immediately below P668 even coverage. -/
structure EvenSupportCodeSurjectivityBoundaryCertificate where
  p668_boundary :
    PrimeShadowEvenCoverageBoundaryCertificate
  even_support_code_surjective :
    SupportIndexedPrimeShadowProducer -> Prop
  surjective_implies_coverage :
    ∀ B : SupportIndexedPrimeShadowProducer,
      even_support_code_surjective B -> PrimeShadowEvenArithmeticCoverage B
  coverage_iff_surjective :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenArithmeticCoverage B ↔
        even_support_code_surjective B
  surjective_iff_goldbach_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      even_support_code_surjective B ->
        (EvenGoldbachStatement ↔
          PrimeShadowCoveredEvenH1NoObstruction B)
  surjective_injective_iff_liftable_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      even_support_code_surjective B ->
        Function.Injective B.producer.arithmeticShadow ->
          (EvenGoldbachStatement ↔
            PrimeShadowEvenLiftableH1NoObstruction B)
  coverage_injective_iff_liftable_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenArithmeticCoverage B ->
        Function.Injective B.producer.arithmeticShadow ->
          (EvenGoldbachStatement ↔
            PrimeShadowEvenLiftableH1NoObstruction B)
  truth_value_shadow_not_structured :
    Not
      (Nonempty
        (StructuredConcreteAdmissiblePrimeShadowBridge
          truthValuePrimeShadowProducer))

/-- DEFINITION 6: the canonical P669 support-code surjectivity boundary. -/
def evenSupportCodeSurjectivityBoundaryCertificate :
    EvenSupportCodeSurjectivityBoundaryCertificate where
  p668_boundary := primeShadowEvenCoverageBoundaryCertificate
  even_support_code_surjective := PrimeShadowEvenSupportCodeSurjective
  surjective_implies_coverage :=
    primeShadowEvenArithmeticCoverage_of_evenSupportCodeSurjective
  coverage_iff_surjective :=
    primeShadowEvenArithmeticCoverage_iff_evenSupportCodeSurjective
  surjective_iff_goldbach_h1 :=
    evenGoldbach_iff_coveredEvenH1_of_evenSupportCodeSurjective
  surjective_injective_iff_liftable_h1 :=
    evenGoldbach_iff_evenLiftableH1_of_evenSupportCodeSurjective_and_injective
  coverage_injective_iff_liftable_h1 :=
    evenGoldbach_iff_evenLiftableH1_of_primeShadowCoverage_and_injective
  truth_value_shadow_not_structured :=
    truthValuePrimeShadowProducer_not_structuredBridge

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P669's support-code producer boundary welded
below the P668 even-coverage boundary. -/
structure EvenSupportCodeProducerBoundaryUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  even_coverage_root :
    EvenCoverageHolyGrailBoundaryUnifiedRootCertificate E
  support_code_boundary :
    EvenSupportCodeSurjectivityBoundaryCertificate
  support_code_surjective_implies_coverage :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        PrimeShadowEvenArithmeticCoverage B
  support_code_surjective_iff_coverage :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenArithmeticCoverage B ↔
        PrimeShadowEvenSupportCodeSurjective B
  support_code_surjective_iff_goldbach_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        (EvenGoldbachStatement ↔
          PrimeShadowCoveredEvenH1NoObstruction B)
  support_code_surjective_injective_iff_liftable_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        Function.Injective B.producer.arithmeticShadow ->
          (EvenGoldbachStatement ↔
            PrimeShadowEvenLiftableH1NoObstruction B)
  even_coverage_injective_iff_liftable_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenArithmeticCoverage B ->
        Function.Injective B.producer.arithmeticShadow ->
          (EvenGoldbachStatement ↔
            PrimeShadowEvenLiftableH1NoObstruction B)
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 7: the current central root with the P669 producer boundary. -/
def evenSupportCodeProducerBoundaryUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    EvenSupportCodeProducerBoundaryUnifiedRootCertificate E where
  even_coverage_root :=
    evenCoverageHolyGrailBoundaryUnifiedRootCertificate (E := E)
  support_code_boundary :=
    evenSupportCodeSurjectivityBoundaryCertificate
  support_code_surjective_implies_coverage :=
    primeShadowEvenArithmeticCoverage_of_evenSupportCodeSurjective
  support_code_surjective_iff_coverage :=
    primeShadowEvenArithmeticCoverage_iff_evenSupportCodeSurjective
  support_code_surjective_iff_goldbach_h1 :=
    evenGoldbach_iff_coveredEvenH1_of_evenSupportCodeSurjective
  support_code_surjective_injective_iff_liftable_h1 :=
    evenGoldbach_iff_evenLiftableH1_of_evenSupportCodeSurjective_and_injective
  even_coverage_injective_iff_liftable_h1 :=
    evenGoldbach_iff_evenLiftableH1_of_primeShadowCoverage_and_injective
  alpha_s_residual :=
    evenCoverageHolyGrailBoundaryUnifiedRootCertificate (E := E)
      |>.alpha_s_residual

end GrandUnification
end SaturationMonoid
