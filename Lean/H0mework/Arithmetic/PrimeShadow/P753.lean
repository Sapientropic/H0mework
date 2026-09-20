import H0mework.Arithmetic.PrimeShadow.P752
import H0mework.Arithmetic.PrimeShadow.P329

/-!
# Proposition 753: actual representatives are explicit prime-pair producers

P752 proves that, after the natural-coded source is fixed, every actual H¹ /
Euler-pullback representative front is exactly ordinary even Goldbach.

This file lowers that remaining content one more step.  Ordinary even
Goldbach is not left as a bare proposition: it is equivalent to a global
producer that returns, for every even exponent `2*n`, an explicit pair of
prime exponents whose sum is that exponent.  The finite search surface from
P329 is also equivalent to the same producer.

Thus the post-P752 target is fully concrete:

`actual H¹ representative producer = global prime-pair producer`.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Explicit global prime-pair producer -/

/-- A function-shaped global Goldbach producer: for every ordinary even
exponent `2*n`, `n >= 2`, return an explicit pair of prime exponents whose
sum is that exponent. -/
structure EvenGoldbachPrimePairProducer where
  pick : (n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent
  sum_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      2 * n = (pick n hn).1.1 + (pick n hn).2.1

/-- THEOREM 1: an explicit prime-pair producer is exactly ordinary even
Goldbach. -/
theorem evenGoldbachPrimePairProducer_iff_goldbach :
    Nonempty EvenGoldbachPrimePairProducer ↔ EvenGoldbachStatement := by
  constructor
  · rintro ⟨P⟩ n hn
    exact ⟨(P.pick n hn).1, (P.pick n hn).2, P.sum_pick n hn⟩
  · intro hgold
    classical
    let p : (n : ℕ) -> 2 ≤ n -> PrimeExponent :=
      fun n hn => Classical.choose (hgold n hn)
    let q : (n : ℕ) -> 2 ≤ n -> PrimeExponent :=
      fun n hn => Classical.choose (Classical.choose_spec (hgold n hn))
    have hsum :
        ∀ (n : ℕ) (hn : 2 ≤ n),
          2 * n = (p n hn).1 + (q n hn).1 := by
      intro n hn
      exact Classical.choose_spec (Classical.choose_spec (hgold n hn))
    exact
      ⟨{
        pick := fun n hn => (p n hn, q n hn)
        sum_pick := hsum
      }⟩

/-! ## Global search success is the same producer content -/

/-- The P329 typed direct search succeeds for every ordinary even exponent.
-/
def EvenGoldbachSearchSuccess : Prop :=
  ∀ n : ℕ, 2 ≤ n -> (goldbachSearchPrimePair (2 * n)).isSome = true

/-- THEOREM 2: global typed-search success is exactly ordinary even Goldbach.
-/
theorem evenGoldbachSearchSuccess_iff_goldbach :
    EvenGoldbachSearchSuccess ↔ EvenGoldbachStatement := by
  constructor
  · intro h n hn
    exact (goldbachSearchPrimePair_isSome_iff (2 * n)).mp (h n hn)
  · intro h n hn
    exact (goldbachSearchPrimePair_isSome_iff (2 * n)).mpr (h n hn)

/-- THEOREM 3: global typed-search success is exactly the explicit prime-pair
producer. -/
theorem evenGoldbachSearchSuccess_iff_primePairProducer :
    EvenGoldbachSearchSuccess ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact
    evenGoldbachSearchSuccess_iff_goldbach.trans
      evenGoldbachPrimePairProducer_iff_goldbach.symm

/-! ## P752 actual fronts as explicit prime-pair producers -/

/-- THEOREM 4: natural-coded even no-obstruction range is exactly an explicit
prime-pair producer. -/
theorem naturalCodedEvenNoObstructionSurjective_iff_primePairProducer :
    SpectralExponentEvenNoObstructionSurjective
        naturalCodedSpectralExponentAdapter ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact
    naturalCodedEvenNoObstructionSurjective_iff_goldbach.trans
      evenGoldbachPrimePairProducer_iff_goldbach.symm

/-- THEOREM 5: the natural-coded adapter-side representative producer is
exactly an explicit prime-pair producer. -/
theorem naturalCodedAdapterRepresentativeProducer_iff_primePairProducer :
    Nonempty
        (SpectralEvenNoObstructionRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact
    naturalCodedAdapterRepresentativeProducer_iff_goldbach.trans
      evenGoldbachPrimePairProducer_iff_goldbach.symm

/-- THEOREM 6: natural-coded liftable H¹ no-obstruction is exactly an explicit
prime-pair producer. -/
theorem naturalCodedLiftableH1_iff_primePairProducer :
    CodedDescentEvenLiftableH1NoObstruction
        naturalCodedSpectralExponentAdapter ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact
    naturalCodedLiftableH1_iff_goldbach.trans
      evenGoldbachPrimePairProducer_iff_goldbach.symm

/-- THEOREM 7: the natural-coded support-indexed representative producer is
exactly an explicit prime-pair producer. -/
theorem naturalCodedSupportIndexedRepresentativeProducer_iff_primePairProducer :
    Nonempty
        (SupportIndexedEvenNoObstructionRepresentativeProducer
          naturalCodedSupportIndexedPrimeShadowProducer) ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact
    naturalCodedSupportIndexedRepresentativeProducer_iff_goldbach.trans
      evenGoldbachPrimePairProducer_iff_goldbach.symm

/-- THEOREM 8: the natural-coded P676 source pullback producer is exactly an
explicit prime-pair producer. -/
theorem naturalCodedSourcePullbackProducer_iff_primePairProducer :
    Nonempty naturalCodedEvenSupportCodeSource.PullbackProducer ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact
    naturalCodedEvenSupportCodeSource_pullbackProducer_iff_goldbach.trans
      evenGoldbachPrimePairProducer_iff_goldbach.symm

/-- THEOREM 9: the natural-coded coded-descent Euler-pullback producer is
exactly an explicit prime-pair producer. -/
theorem naturalCodedEulerPullbackRepresentativeProducer_iff_primePairProducer :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact
    naturalCodedEulerPullbackRepresentativeProducer_iff_goldbach.trans
      evenGoldbachPrimePairProducer_iff_goldbach.symm

/-- THEOREM 10: the natural-coded coded-descent Euler-pullback producer is
exactly global P329 typed-search success. -/
theorem naturalCodedEulerPullbackRepresentativeProducer_iff_searchSuccess :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachSearchSuccess := by
  exact
    naturalCodedEulerPullbackRepresentativeProducer_iff_goldbach.trans
      evenGoldbachSearchSuccess_iff_goldbach.symm

/-! ## Packaged explicit-producer certificate -/

/-- P753 certificate: the remaining actual H¹ / Euler-pullback content is an
explicit global prime-pair producer, equivalently global success of the typed
finite search from P329. -/
structure NaturalCodedExplicitPrimePairProducerCertificate where
  p752_maximality : NaturalCodedActualProducerMaximalityCertificate
  prime_pair_producer : Type
  prime_pair_producer_iff_goldbach :
    Nonempty prime_pair_producer ↔ EvenGoldbachStatement
  search_success : Prop
  search_success_iff_goldbach :
    search_success ↔ EvenGoldbachStatement
  search_success_iff_prime_pair_producer :
    search_success ↔ Nonempty prime_pair_producer
  no_obstruction_range_iff_prime_pair_producer :
    SpectralExponentEvenNoObstructionSurjective
        naturalCodedSpectralExponentAdapter ↔
      Nonempty prime_pair_producer
  adapter_representative_iff_prime_pair_producer :
    Nonempty
        (SpectralEvenNoObstructionRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      Nonempty prime_pair_producer
  liftable_h1_iff_prime_pair_producer :
    CodedDescentEvenLiftableH1NoObstruction
        naturalCodedSpectralExponentAdapter ↔
      Nonempty prime_pair_producer
  support_indexed_representative_iff_prime_pair_producer :
    Nonempty
        (SupportIndexedEvenNoObstructionRepresentativeProducer
          naturalCodedSupportIndexedPrimeShadowProducer) ↔
      Nonempty prime_pair_producer
  source_pullback_iff_prime_pair_producer :
    Nonempty naturalCodedEvenSupportCodeSource.PullbackProducer ↔
      Nonempty prime_pair_producer
  euler_pullback_iff_prime_pair_producer :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      Nonempty prime_pair_producer
  euler_pullback_iff_search_success :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      search_success

/-- THEOREM 11: canonical P753 explicit prime-pair producer certificate. -/
def naturalCodedExplicitPrimePairProducerCertificate :
    NaturalCodedExplicitPrimePairProducerCertificate where
  p752_maximality := naturalCodedActualProducerMaximalityCertificate
  prime_pair_producer := EvenGoldbachPrimePairProducer
  prime_pair_producer_iff_goldbach :=
    evenGoldbachPrimePairProducer_iff_goldbach
  search_success := EvenGoldbachSearchSuccess
  search_success_iff_goldbach := evenGoldbachSearchSuccess_iff_goldbach
  search_success_iff_prime_pair_producer :=
    evenGoldbachSearchSuccess_iff_primePairProducer
  no_obstruction_range_iff_prime_pair_producer :=
    naturalCodedEvenNoObstructionSurjective_iff_primePairProducer
  adapter_representative_iff_prime_pair_producer :=
    naturalCodedAdapterRepresentativeProducer_iff_primePairProducer
  liftable_h1_iff_prime_pair_producer :=
    naturalCodedLiftableH1_iff_primePairProducer
  support_indexed_representative_iff_prime_pair_producer :=
    naturalCodedSupportIndexedRepresentativeProducer_iff_primePairProducer
  source_pullback_iff_prime_pair_producer :=
    naturalCodedSourcePullbackProducer_iff_primePairProducer
  euler_pullback_iff_prime_pair_producer :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_primePairProducer
  euler_pullback_iff_search_success :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_searchSuccess

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The unified root after P753: the remaining actual front is an explicit
global prime-pair producer / global P329 search-success producer. -/
structure NaturalCodedExplicitPrimePairProducerRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p752_root :
    NaturalCodedActualProducerMaximalityRootCertificate E
  explicit_prime_pair :
    NaturalCodedExplicitPrimePairProducerCertificate
  prime_pair_producer_iff_goldbach :
    Nonempty EvenGoldbachPrimePairProducer ↔ EvenGoldbachStatement
  search_success_iff_goldbach :
    EvenGoldbachSearchSuccess ↔ EvenGoldbachStatement
  euler_pullback_iff_prime_pair_producer :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      Nonempty EvenGoldbachPrimePairProducer
  euler_pullback_iff_search_success :
    Nonempty
        (CodedDescentEulerPullbackRepresentativeProducer
          naturalCodedSpectralExponentAdapter) ↔
      EvenGoldbachSearchSuccess
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 12: root certificate with the explicit prime-pair producer normal
form. -/
def naturalCodedExplicitPrimePairProducerRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    NaturalCodedExplicitPrimePairProducerRootCertificate E where
  p752_root := naturalCodedActualProducerMaximalityRootCertificate (E := E)
  explicit_prime_pair :=
    naturalCodedExplicitPrimePairProducerCertificate
  prime_pair_producer_iff_goldbach :=
    evenGoldbachPrimePairProducer_iff_goldbach
  search_success_iff_goldbach :=
    evenGoldbachSearchSuccess_iff_goldbach
  euler_pullback_iff_prime_pair_producer :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_primePairProducer
  euler_pullback_iff_search_success :=
    naturalCodedEulerPullbackRepresentativeProducer_iff_searchSuccess
  alpha_s_residual :=
    (naturalCodedActualProducerMaximalityRootCertificate
      (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
