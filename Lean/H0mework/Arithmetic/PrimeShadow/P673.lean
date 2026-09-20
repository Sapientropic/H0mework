import H0mework.Arithmetic.PrimeShadow.P672

/-!
# Proposition 673: support-indexed no-obstructed representatives

P672 gives the concrete function-shaped producer for a total
`SpectralExponentCodeAdapter`.  But P546/P623 identify the honest final
Euler/RH front door as support-indexed: unsupported H¹ points should not be
silently assigned exponent codes.

This file moves the representative-producer interface onto that honest
support-indexed prime-shadow front door.  A supported producer supplies, for
each ordinary even exponent, a supported spectral representative, the exact
supported code equality, and H¹ no-obstruction.

Lean proves that this support-indexed producer is exactly support-code range
plus ordinary even Goldbach.  Under arithmetic-shadow injectivity it is also
equivalent to H¹ no-obstruction on the actual supported-liftable Euler
pullback domain.  Thus the final Euler/RH producer debt is now pinned to the
real support-indexed object, not to the totalized adapter convenience layer.

Boundary: this still does not construct the final Euler/RH support.  It proves
the exact support-indexed function certificate that such a construction must
inhabit.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Support-indexed representative producer -/

/-- A support-indexed no-obstructed representative producer for the even
ordinary exponents.

Unlike P672, this producer does not require a total spectral code.  It chooses
only supported spectral points of a `SupportIndexedPrimeShadowProducer`. -/
structure SupportIndexedEvenNoObstructionRepresentativeProducer
    (B : SupportIndexedPrimeShadowProducer) where
  pick :
    (n : ℕ) -> 2 ≤ n -> H1SpectralProjection (1 / 2 : ℝ)
  support_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n), B.support (pick n hn)
  code_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      B.code (pick n hn) (support_pick n hn) = 2 * n
  no_obstruction_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      H1SpectralNoObstructionComplete (pick n hn)

/-- THEOREM 1: a support-indexed representative producer gives the P669
support-code surjectivity predicate. -/
theorem supportCodeSurjective_of_supportedRepresentativeProducer
    (B : SupportIndexedPrimeShadowProducer)
    (P : SupportIndexedEvenNoObstructionRepresentativeProducer B) :
    PrimeShadowEvenSupportCodeSurjective B := by
  intro n hn
  exact ⟨P.pick n hn, P.support_pick n hn, P.code_pick n hn⟩

/-- THEOREM 2: a support-indexed representative producer proves ordinary even
Goldbach through the common-predicate pullback of the prime-shadow producer.
-/
theorem evenGoldbach_of_supportedRepresentativeProducer
    (B : SupportIndexedPrimeShadowProducer)
    (P : SupportIndexedEvenNoObstructionRepresentativeProducer B) :
    EvenGoldbachStatement := by
  intro n hn
  let s := P.pick n hn
  let hs : B.support s := P.support_pick n hn
  have hcommon :
      (B.toCommonPredicateProducer).commonComplete (B.code s hs) :=
    ((B.toCommonPredicateProducer).common_spectral s hs).mpr
      (P.no_obstruction_pick n hn)
  have hdecomp :
      HasPrimeAdditiveDecomposition (B.code s hs) :=
    ((B.toCommonPredicateProducer).common_arithmetic (B.code s hs)).mp
      hcommon
  simpa [s, hs, P.code_pick n hn] using hdecomp

/-- THEOREM 3: a support-indexed representative producer directly supplies
H¹ no-obstruction on the actual supported-liftable even Euler-pullback domain.
-/
theorem evenLiftableH1_of_supportedRepresentativeProducer
    (B : SupportIndexedPrimeShadowProducer)
    (P : SupportIndexedEvenNoObstructionRepresentativeProducer B) :
    PrimeShadowEvenLiftableH1NoObstruction B := by
  intro n hn
  let s := P.pick n hn
  let hs : B.support s := P.support_pick n hn
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
  have hallowed :
      SupportedCodedDescentAllowed
        (B.toCommonPredicateProducer.toSupportedSpectralExponentCodeProducer)
        x0 := by
    refine ⟨hsx, ?_⟩
    change
      SigmaExponentImage.exponent x0.arithmetic =
        B.code x0.spectral hsx
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
      _ = B.code s hs := (P.code_pick n hn).symm
      _ = B.code x0.spectral hsx := by
            cases hspectral
            congr
  let xd : CommonPredicateSupportedCodedDomain B.toCommonPredicateProducer :=
    ⟨x0, hallowed⟩
  have hlift : PrimeShadowSupportedLiftable B xd.1 :=
    commonPredicateSupportedCodedDomain_subset_primeShadowLiftable B xd
  refine ⟨⟨xd.1, hlift⟩, harith, ?_⟩
  simpa [xd, x0, hspectral] using P.no_obstruction_pick n hn

/-- THEOREM 4: support-code range plus ordinary even Goldbach upgrades to a
function-shaped support-indexed representative producer. -/
theorem supportedRepresentativeProducer_of_supportCodeSurjective_and_goldbach
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B)
    (hgold : EvenGoldbachStatement) :
    Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B) := by
  classical
  let pick :
      (n : ℕ) -> 2 ≤ n -> H1SpectralProjection (1 / 2 : ℝ) :=
    fun n hn => Classical.choose (hsurj n hn)
  let support_pick :
      ∀ (n : ℕ) (hn : 2 ≤ n), B.support (pick n hn) :=
    fun n hn => (Classical.choose_spec (hsurj n hn)).1
  have code_pick :
      ∀ (n : ℕ) (hn : 2 ≤ n),
        B.code (pick n hn) (support_pick n hn) = 2 * n := by
    intro n hn
    exact (Classical.choose_spec (hsurj n hn)).2
  have no_obstruction_pick :
      ∀ (n : ℕ) (hn : 2 ≤ n),
        H1SpectralNoObstructionComplete (pick n hn) := by
    intro n hn
    let s := pick n hn
    let hs : B.support s := support_pick n hn
    have hdecomp :
        HasPrimeAdditiveDecomposition (B.code s hs) := by
      simpa [s, hs, code_pick n hn] using hgold n hn
    have hcommon :
        (B.toCommonPredicateProducer).commonComplete (B.code s hs) :=
      ((B.toCommonPredicateProducer).common_arithmetic (B.code s hs)).mpr
        hdecomp
    exact
      ((B.toCommonPredicateProducer).common_spectral s hs).mp hcommon
  exact
    ⟨{
      pick := pick
      support_pick := support_pick
      code_pick := code_pick
      no_obstruction_pick := no_obstruction_pick
    }⟩

/-- THEOREM 5: a support-indexed representative producer is exactly
support-code range plus ordinary even Goldbach. -/
theorem supportedRepresentativeProducer_iff_supportCodeSurjective_and_goldbach
    (B : SupportIndexedPrimeShadowProducer) :
    Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B) ↔
      PrimeShadowEvenSupportCodeSurjective B ∧ EvenGoldbachStatement := by
  constructor
  · rintro ⟨P⟩
    exact
      ⟨supportCodeSurjective_of_supportedRepresentativeProducer B P,
        evenGoldbach_of_supportedRepresentativeProducer B P⟩
  · rintro ⟨hsurj, hgold⟩
    exact
      supportedRepresentativeProducer_of_supportCodeSurjective_and_goldbach
        B hsurj hgold

/-- THEOREM 6: once support-code range is supplied, ordinary even Goldbach is
exactly the existence of a support-indexed representative producer. -/
theorem evenGoldbach_iff_supportedRepresentativeProducer_of_supportCodeSurjective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B) :
    EvenGoldbachStatement ↔
      Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B) := by
  constructor
  · intro hgold
    exact
      supportedRepresentativeProducer_of_supportCodeSurjective_and_goldbach
        B hsurj hgold
  · rintro ⟨P⟩
    exact evenGoldbach_of_supportedRepresentativeProducer B P

/-- THEOREM 7: with support-code range and arithmetic-shadow injectivity, the
support-indexed representative producer is equivalent to H¹ no-obstruction on
the actual supported-liftable Euler-pullback domain. -/
theorem supportedRepresentativeProducer_iff_evenLiftableH1_of_supportCodeSurjective_and_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B)
    (hinj : Function.Injective B.producer.arithmeticShadow) :
    Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B) ↔
      PrimeShadowEvenLiftableH1NoObstruction B := by
  exact
    (evenGoldbach_iff_supportedRepresentativeProducer_of_supportCodeSurjective
      B hsurj).symm.trans
      (evenGoldbach_iff_evenLiftableH1_of_evenSupportCodeSurjective_and_injective
        B hsurj hinj)

/-! ## Packaged support-indexed producer boundary -/

/-- The P673 certificate: the final mathematical producer interface is
support-indexed, function-shaped, and equivalent to support-code range plus
Goldbach, and under injectivity equivalent to the liftable Euler-pullback H¹
condition. -/
structure SupportIndexedRepresentativeProducerBoundaryCertificate where
  p672_totalized_boundary :
    AdapterRepresentativeProducerBoundaryCertificate
  representative_producer :
    SupportIndexedPrimeShadowProducer -> Type
  producer_iff_support_range_and_goldbach :
    ∀ B : SupportIndexedPrimeShadowProducer,
      Nonempty (representative_producer B) ↔
        PrimeShadowEvenSupportCodeSurjective B ∧ EvenGoldbachStatement
  goldbach_iff_producer_of_support_range :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        (EvenGoldbachStatement ↔ Nonempty (representative_producer B))
  producer_implies_liftable_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      Nonempty (representative_producer B) ->
        PrimeShadowEvenLiftableH1NoObstruction B
  producer_iff_liftable_h1_of_support_range_and_injective :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        Function.Injective B.producer.arithmeticShadow ->
          (Nonempty (representative_producer B) ↔
            PrimeShadowEvenLiftableH1NoObstruction B)

/-- DEFINITION 2: the canonical P673 support-indexed representative producer
boundary. -/
def supportIndexedRepresentativeProducerBoundaryCertificate :
    SupportIndexedRepresentativeProducerBoundaryCertificate where
  p672_totalized_boundary := adapterRepresentativeProducerBoundaryCertificate
  representative_producer :=
    SupportIndexedEvenNoObstructionRepresentativeProducer
  producer_iff_support_range_and_goldbach :=
    supportedRepresentativeProducer_iff_supportCodeSurjective_and_goldbach
  goldbach_iff_producer_of_support_range :=
    evenGoldbach_iff_supportedRepresentativeProducer_of_supportCodeSurjective
  producer_implies_liftable_h1 := by
    intro B hP
    rcases hP with ⟨P⟩
    exact evenLiftableH1_of_supportedRepresentativeProducer B P
  producer_iff_liftable_h1_of_support_range_and_injective :=
    supportedRepresentativeProducer_iff_evenLiftableH1_of_supportCodeSurjective_and_injective

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P673's honest support-indexed representative
producer boundary welded below P672's total-adapter convenience layer. -/
structure SupportIndexedRepresentativeProducerUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p672_root :
    RepresentativeProducerUnifiedRootCertificate E
  support_indexed_boundary :
    SupportIndexedRepresentativeProducerBoundaryCertificate
  producer_iff_support_range_and_goldbach :
    ∀ B : SupportIndexedPrimeShadowProducer,
      Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B) ↔
        PrimeShadowEvenSupportCodeSurjective B ∧ EvenGoldbachStatement
  producer_iff_liftable_h1_of_support_range_and_injective :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        Function.Injective B.producer.arithmeticShadow ->
          (Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B) ↔
            PrimeShadowEvenLiftableH1NoObstruction B)
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 8: the current central root with the P673 support-indexed
representative producer boundary. -/
def supportIndexedRepresentativeProducerUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    SupportIndexedRepresentativeProducerUnifiedRootCertificate E where
  p672_root := representativeProducerUnifiedRootCertificate (E := E)
  support_indexed_boundary :=
    supportIndexedRepresentativeProducerBoundaryCertificate
  producer_iff_support_range_and_goldbach :=
    supportedRepresentativeProducer_iff_supportCodeSurjective_and_goldbach
  producer_iff_liftable_h1_of_support_range_and_injective :=
    supportedRepresentativeProducer_iff_evenLiftableH1_of_supportCodeSurjective_and_injective
  alpha_s_residual :=
    (representativeProducerUnifiedRootCertificate (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
