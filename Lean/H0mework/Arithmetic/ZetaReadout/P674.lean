import H0mework.Arithmetic.PrimeShadow.P673

/-!
# Proposition 674: actual Euler-pullback representatives

P673 moves the final representative-producer interface onto the honest
support-indexed prime-shadow front door.  This file lowers it one final
geometric step: the producer may be read as choosing actual points of the
supported-liftable Euler pullback domain.

Thus the remaining Goldbach/RH producer debt is no longer phrased as a total
adapter, nor merely as a supported spectral chooser.  It is a function that,
for each ordinary even exponent, produces a supported-liftable seven-facet
state whose arithmetic projection is that even half-sigma point and whose
spectral projection has no H¹ obstruction.

Boundary: this still does not construct the final Euler/RH support.  It proves
the exact pullback-domain object that such a construction must inhabit.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Euler-pullback representative producer -/

/-- A concrete representative producer living in the actual supported-liftable
Euler pullback domain.

Each output is not merely a spectral point plus a code equality; it is a
seven-facet state already certified as `PrimeShadowSupportedLiftable`. -/
structure EvenEulerPullbackRepresentativeProducer
    (B : SupportIndexedPrimeShadowProducer) where
  pick :
    (n : ℕ) -> 2 ≤ n ->
      { x : ArithmeticAdmissibleSevenFacet //
          PrimeShadowSupportedLiftable B x }
  arithmetic_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      (pick n hn).1.arithmetic = evenHalfSigmaArithmeticPoint n
  no_obstruction_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      H1SpectralNoObstructionComplete (pick n hn).1.spectral

/-- THEOREM 1: an Euler-pullback representative producer is exactly a witness
for H¹ no-obstruction on the actual supported-liftable even domain. -/
theorem liftableH1_of_eulerPullbackRepresentativeProducer
    (B : SupportIndexedPrimeShadowProducer)
    (P : EvenEulerPullbackRepresentativeProducer B) :
    PrimeShadowEvenLiftableH1NoObstruction B := by
  intro n hn
  exact
    ⟨P.pick n hn, P.arithmetic_pick n hn, P.no_obstruction_pick n hn⟩

/-- THEOREM 2: H¹ no-obstruction on the actual supported-liftable even domain
can be repackaged as a function-shaped Euler-pullback producer. -/
theorem eulerPullbackRepresentativeProducer_of_liftableH1
    (B : SupportIndexedPrimeShadowProducer)
    (h : PrimeShadowEvenLiftableH1NoObstruction B) :
    Nonempty (EvenEulerPullbackRepresentativeProducer B) := by
  classical
  let pick :
      (n : ℕ) -> 2 ≤ n ->
        { x : ArithmeticAdmissibleSevenFacet //
            PrimeShadowSupportedLiftable B x } :=
    fun n hn => Classical.choose (h n hn)
  have arithmetic_pick :
      ∀ (n : ℕ) (hn : 2 ≤ n),
        (pick n hn).1.arithmetic = evenHalfSigmaArithmeticPoint n := by
    intro n hn
    exact (Classical.choose_spec (h n hn)).1
  have no_obstruction_pick :
      ∀ (n : ℕ) (hn : 2 ≤ n),
        H1SpectralNoObstructionComplete (pick n hn).1.spectral := by
    intro n hn
    exact (Classical.choose_spec (h n hn)).2
  exact
    ⟨{
      pick := pick
      arithmetic_pick := arithmetic_pick
      no_obstruction_pick := no_obstruction_pick
    }⟩

/-- THEOREM 3: the pullback-domain producer is equivalent to H¹
no-obstruction on the actual supported-liftable even domain. -/
theorem eulerPullbackRepresentativeProducer_iff_liftableH1
    (B : SupportIndexedPrimeShadowProducer) :
    Nonempty (EvenEulerPullbackRepresentativeProducer B) ↔
      PrimeShadowEvenLiftableH1NoObstruction B := by
  constructor
  · rintro ⟨P⟩
    exact liftableH1_of_eulerPullbackRepresentativeProducer B P
  · exact eulerPullbackRepresentativeProducer_of_liftableH1 B

/-- THEOREM 4: with support-code range and arithmetic-shadow injectivity,
ordinary even Goldbach is exactly the existence of actual Euler-pullback
representatives. -/
theorem evenGoldbach_iff_eulerPullbackRepresentativeProducer_of_supportCodeSurjective_and_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B)
    (hinj : Function.Injective B.producer.arithmeticShadow) :
    EvenGoldbachStatement ↔
      Nonempty (EvenEulerPullbackRepresentativeProducer B) := by
  exact
    (evenGoldbach_iff_evenLiftableH1_of_evenSupportCodeSurjective_and_injective
      B hsurj hinj).trans
      (eulerPullbackRepresentativeProducer_iff_liftableH1 B).symm

/-- THEOREM 5: under the same range and injectivity hypotheses, the P673
support-indexed spectral producer and the P674 Euler-pullback producer are the
same remaining producer debt. -/
theorem eulerPullbackRepresentativeProducer_iff_supportedRepresentativeProducer_of_supportCodeSurjective_and_injective
    (B : SupportIndexedPrimeShadowProducer)
    (hsurj : PrimeShadowEvenSupportCodeSurjective B)
    (hinj : Function.Injective B.producer.arithmeticShadow) :
    Nonempty (EvenEulerPullbackRepresentativeProducer B) ↔
      Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B) := by
  exact
    (eulerPullbackRepresentativeProducer_iff_liftableH1 B).trans
      (supportedRepresentativeProducer_iff_evenLiftableH1_of_supportCodeSurjective_and_injective
        B hsurj hinj).symm

/-! ## Packaged pullback-domain producer boundary -/

/-- The P674 certificate: the final producer can be read as actual
Euler-pullback representatives, equivalent to liftable H¹ no-obstruction and,
under the P669/P624 hypotheses, equivalent to P673's support-indexed producer
and ordinary even Goldbach. -/
structure EulerPullbackRepresentativeProducerBoundaryCertificate where
  p673_support_indexed_boundary :
    SupportIndexedRepresentativeProducerBoundaryCertificate
  euler_pullback_producer :
    SupportIndexedPrimeShadowProducer -> Type
  producer_iff_liftable_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      Nonempty (euler_pullback_producer B) ↔
        PrimeShadowEvenLiftableH1NoObstruction B
  goldbach_iff_producer_of_support_range_and_injective :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        Function.Injective B.producer.arithmeticShadow ->
          (EvenGoldbachStatement ↔ Nonempty (euler_pullback_producer B))
  producer_iff_supported_representative_of_support_range_and_injective :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        Function.Injective B.producer.arithmeticShadow ->
          (Nonempty (euler_pullback_producer B) ↔
            Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B))

/-- DEFINITION 1: the canonical P674 pullback-domain representative-producer
boundary. -/
def eulerPullbackRepresentativeProducerBoundaryCertificate :
    EulerPullbackRepresentativeProducerBoundaryCertificate where
  p673_support_indexed_boundary :=
    supportIndexedRepresentativeProducerBoundaryCertificate
  euler_pullback_producer := EvenEulerPullbackRepresentativeProducer
  producer_iff_liftable_h1 :=
    eulerPullbackRepresentativeProducer_iff_liftableH1
  goldbach_iff_producer_of_support_range_and_injective :=
    evenGoldbach_iff_eulerPullbackRepresentativeProducer_of_supportCodeSurjective_and_injective
  producer_iff_supported_representative_of_support_range_and_injective :=
    eulerPullbackRepresentativeProducer_iff_supportedRepresentativeProducer_of_supportCodeSurjective_and_injective

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P674's actual Euler-pullback representative
producer boundary welded below P673's support-indexed spectral front door. -/
structure EulerPullbackRepresentativeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p673_root :
    SupportIndexedRepresentativeProducerUnifiedRootCertificate E
  euler_pullback_boundary :
    EulerPullbackRepresentativeProducerBoundaryCertificate
  producer_iff_liftable_h1 :
    ∀ B : SupportIndexedPrimeShadowProducer,
      Nonempty (EvenEulerPullbackRepresentativeProducer B) ↔
        PrimeShadowEvenLiftableH1NoObstruction B
  producer_iff_supported_representative_of_support_range_and_injective :
    ∀ B : SupportIndexedPrimeShadowProducer,
      PrimeShadowEvenSupportCodeSurjective B ->
        Function.Injective B.producer.arithmeticShadow ->
          (Nonempty (EvenEulerPullbackRepresentativeProducer B) ↔
            Nonempty (SupportIndexedEvenNoObstructionRepresentativeProducer B))
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 6: the current central root with the P674 Euler-pullback
representative-producer boundary. -/
def eulerPullbackRepresentativeUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    EulerPullbackRepresentativeUnifiedRootCertificate E where
  p673_root := supportIndexedRepresentativeProducerUnifiedRootCertificate (E := E)
  euler_pullback_boundary :=
    eulerPullbackRepresentativeProducerBoundaryCertificate
  producer_iff_liftable_h1 :=
    eulerPullbackRepresentativeProducer_iff_liftableH1
  producer_iff_supported_representative_of_support_range_and_injective :=
    eulerPullbackRepresentativeProducer_iff_supportedRepresentativeProducer_of_supportCodeSurjective_and_injective
  alpha_s_residual :=
    (supportIndexedRepresentativeProducerUnifiedRootCertificate (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
