import H0mework.Arithmetic.ZetaReadout.P674

/-!
# Proposition 675: canonical coded-descent pullback normal form

P674 identifies the final mathematical producer as actual representatives in
the supported-liftable Euler pullback domain.  This file removes two remaining
ambient assumptions from that statement.

First, under arithmetic-shadow injectivity, a pullback representative producer
itself forces support-code surjectivity.  Thus the P674 producer is not merely
"Goldbach if range is present"; it is exactly support-code range plus ordinary
even Goldbach.

Second, for the canonical coded-descent support-indexed producer, P625 already
discharges arithmetic-shadow injectivity and P670 identifies support-code
range with adapter even-code range.  Therefore the canonical coded-descent
P674 producer has a compact normal form:

`producer exists ↔ adapter even-code range ∧ ordinary even Goldbach`.

Boundary: this still does not construct the final Euler/RH adapter range or
prove Goldbach/RH.  It proves the exact canonical coded-descent normal form for
the actual Euler-pullback producer.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Pullback representatives force support-code range under injectivity -/

/-- THEOREM 1: once arithmetic shadows are injective, an actual
Euler-pullback representative producer forces support-code surjectivity.

The proof extracts, for each produced liftable seven-facet state, the
supported-coded equality guaranteed by P624's injective pullback converse. -/
theorem supportCodeSurjective_of_eulerPullbackRepresentativeProducer_and_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hinj : Function.Injective B.producer.arithmeticShadow)
    (P : EvenEulerPullbackRepresentativeProducer B) :
    PrimeShadowEvenSupportCodeSurjective B := by
  intro n hn
  let x := P.pick n hn
  have hallowed :
      SupportedCodedDescentAllowed
          (B.toCommonPredicateProducer.toSupportedSpectralExponentCodeProducer)
          x.1 := by
    exact
      (supportedCodedAllowed_iff_primeShadowSupportedLiftable_of_arithmeticShadow_injective
        B hinj x.1).mpr x.2
  rcases hallowed with ⟨hs, hcode⟩
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
        rw [P.arithmetic_pick n hn]
    _ = 2 * n := hexp

/-- THEOREM 2: under arithmetic-shadow injectivity, the actual Euler-pullback
producer is exactly support-code range plus ordinary even Goldbach. -/
theorem eulerPullbackRepresentativeProducer_iff_supportCodeSurjective_and_goldbach_of_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hinj : Function.Injective B.producer.arithmeticShadow) :
    Nonempty (EvenEulerPullbackRepresentativeProducer B) ↔
      PrimeShadowEvenSupportCodeSurjective B ∧ EvenGoldbachStatement := by
  constructor
  · rintro ⟨P⟩
    have hlift : PrimeShadowEvenLiftableH1NoObstruction B :=
      liftableH1_of_eulerPullbackRepresentativeProducer B P
    exact
      ⟨supportCodeSurjective_of_eulerPullbackRepresentativeProducer_and_injective
          B hinj P,
        goldbach_of_evenLiftableH1_and_arithmeticShadow_injective
          B hinj hlift⟩
  · rintro ⟨hsurj, hgold⟩
    exact
      eulerPullbackRepresentativeProducer_of_liftableH1 B
        (evenLiftableH1_of_goldbach_and_evenSupportCodeSurjective
          B hsurj hgold)

/-! ## Canonical coded-descent normal form -/

/-- The P674 producer specialized to the canonical coded-descent
support-indexed producer induced by a spectral exponent adapter. -/
abbrev CodedDescentEulerPullbackRepresentativeProducer
    (A : SpectralExponentCodeAdapter) : Type :=
  EvenEulerPullbackRepresentativeProducer
    (codedDescentSupportIndexedPrimeShadowProducer A)

/-- THEOREM 3: for canonical coded descent, the P674 producer is exactly
adapter even-code range plus ordinary even Goldbach. -/
theorem codedDescentEulerPullbackRepresentativeProducer_iff_adapterEvenCodeRange_and_goldbach
    (A : SpectralExponentCodeAdapter) :
    Nonempty (CodedDescentEulerPullbackRepresentativeProducer A) ↔
      SpectralExponentEvenCodeSurjective A ∧ EvenGoldbachStatement := by
  have hiff :=
    eulerPullbackRepresentativeProducer_iff_supportCodeSurjective_and_goldbach_of_injective
      (codedDescentSupportIndexedPrimeShadowProducer A)
      (codedDescentSupportIndexedPrimeShadowProducer_arithmeticShadow_injective A)
  exact
    hiff.trans
      (and_congr_left' <|
        (codedDescentEvenSupportCodeSurjective_iff_adapterEvenCodeSurjective A))

/-- THEOREM 4: if a coded-descent adapter ranges over all ordinary even
exponents, Goldbach is exactly the existence of actual coded-descent
Euler-pullback representatives. -/
theorem evenGoldbach_iff_codedDescentEulerPullbackRepresentativeProducer_of_adapterEvenCodeRange
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentEvenCodeSurjective A) :
    EvenGoldbachStatement ↔
      Nonempty (CodedDescentEulerPullbackRepresentativeProducer A) := by
  constructor
  · intro hgold
    exact
      (codedDescentEulerPullbackRepresentativeProducer_iff_adapterEvenCodeRange_and_goldbach
        A).mpr ⟨hrange, hgold⟩
  · intro hP
    exact
      ((codedDescentEulerPullbackRepresentativeProducer_iff_adapterEvenCodeRange_and_goldbach
        A).mp hP).2

/-! ## Packaged final normal-form boundary -/

/-- The P675 certificate packages the injective general normal form and its
canonical coded-descent specialization. -/
structure CodedDescentEulerPullbackNormalFormCertificate where
  p674_pullback_boundary :
    EulerPullbackRepresentativeProducerBoundaryCertificate
  general_producer_iff_support_range_and_goldbach_of_injective :
    ∀ B : SupportIndexedPrimeShadowProducer,
      Function.Injective B.producer.arithmeticShadow ->
        (Nonempty (EvenEulerPullbackRepresentativeProducer B) ↔
          PrimeShadowEvenSupportCodeSurjective B ∧ EvenGoldbachStatement)
  coded_descent_producer :
    SpectralExponentCodeAdapter -> Type
  coded_descent_producer_iff_adapter_range_and_goldbach :
    ∀ A : SpectralExponentCodeAdapter,
      Nonempty (coded_descent_producer A) ↔
        SpectralExponentEvenCodeSurjective A ∧ EvenGoldbachStatement
  goldbach_iff_coded_descent_producer_of_adapter_range :
    ∀ A : SpectralExponentCodeAdapter,
      SpectralExponentEvenCodeSurjective A ->
        (EvenGoldbachStatement ↔ Nonempty (coded_descent_producer A))

/-- DEFINITION 1: canonical P675 coded-descent Euler-pullback normal-form
certificate. -/
def codedDescentEulerPullbackNormalFormCertificate :
    CodedDescentEulerPullbackNormalFormCertificate where
  p674_pullback_boundary :=
    eulerPullbackRepresentativeProducerBoundaryCertificate
  general_producer_iff_support_range_and_goldbach_of_injective :=
    eulerPullbackRepresentativeProducer_iff_supportCodeSurjective_and_goldbach_of_injective
  coded_descent_producer := CodedDescentEulerPullbackRepresentativeProducer
  coded_descent_producer_iff_adapter_range_and_goldbach :=
    codedDescentEulerPullbackRepresentativeProducer_iff_adapterEvenCodeRange_and_goldbach
  goldbach_iff_coded_descent_producer_of_adapter_range :=
    evenGoldbach_iff_codedDescentEulerPullbackRepresentativeProducer_of_adapterEvenCodeRange

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P675's canonical coded-descent
Euler-pullback normal form welded below P674. -/
structure CodedDescentEulerPullbackNormalFormUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p674_root :
    EulerPullbackRepresentativeUnifiedRootCertificate E
  coded_descent_normal_form :
    CodedDescentEulerPullbackNormalFormCertificate
  coded_descent_producer_iff_adapter_range_and_goldbach :
    ∀ A : SpectralExponentCodeAdapter,
      Nonempty (CodedDescentEulerPullbackRepresentativeProducer A) ↔
        SpectralExponentEvenCodeSurjective A ∧ EvenGoldbachStatement
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 5: the current central root with P675's coded-descent
Euler-pullback normal form. -/
def codedDescentEulerPullbackNormalFormUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CodedDescentEulerPullbackNormalFormUnifiedRootCertificate E where
  p674_root := eulerPullbackRepresentativeUnifiedRootCertificate (E := E)
  coded_descent_normal_form :=
    codedDescentEulerPullbackNormalFormCertificate
  coded_descent_producer_iff_adapter_range_and_goldbach :=
    codedDescentEulerPullbackRepresentativeProducer_iff_adapterEvenCodeRange_and_goldbach
  alpha_s_residual :=
    (eulerPullbackRepresentativeUnifiedRootCertificate (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
