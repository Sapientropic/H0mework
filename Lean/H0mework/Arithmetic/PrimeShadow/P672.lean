import H0mework.Arithmetic.PrimeShadow.P671

/-!
# Proposition 672: no-obstructed even representatives as an actual producer

P671 proves the no-free-lunch boundary: naming every even exponent is only an
address range.  The actual producer must supply, for every ordinary even
exponent, a spectral representative with that exact code and H¹
no-obstruction.

This file turns that remaining debt from an existential predicate into a
function-shaped certificate.  A producer is not a truth-value oracle for
Goldbach/RH; it is a chooser of spectral representatives, together with the
two audited fields that make the representative usable:

* its adapter code is the requested even exponent;
* its H¹ spectral obstruction is absent.

Lean proves that such a producer is equivalent to P671's no-obstruction range,
and therefore, under the same adapter even-code range condition, exactly as
strong as ordinary even Goldbach and the coded-descent liftable H¹ condition.

Boundary: this still does not construct the final Euler/RH spectral adapter.
It pins the final producer interface as a concrete function certificate rather
than a loose slogan or a result-shaped compatibility field.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Representative producer -/

/-- A concrete no-obstructed representative producer for the even part of a
spectral exponent adapter.

For every `n >= 2`, `pick n hn` must be a spectral point whose code is the
ordinary even exponent `2 * n`, and whose H¹ obstruction is absent. -/
structure SpectralEvenNoObstructionRepresentativeProducer
    (A : SpectralExponentCodeAdapter) where
  pick :
    (n : ℕ) -> 2 ≤ n -> H1SpectralProjection (1 / 2 : ℝ)
  code_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n), A.code (pick n hn) = 2 * n
  no_obstruction_pick :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      H1SpectralNoObstructionComplete (pick n hn)

/-- THEOREM 1: a function-shaped representative producer gives P671's
no-obstruction range predicate. -/
theorem evenNoObstructionRange_of_representativeProducer
    (A : SpectralExponentCodeAdapter)
    (P : SpectralEvenNoObstructionRepresentativeProducer A) :
    SpectralExponentEvenNoObstructionSurjective A := by
  intro n hn
  exact ⟨P.pick n hn, P.code_pick n hn, P.no_obstruction_pick n hn⟩

/-- THEOREM 2: P671's no-obstruction range predicate can be repackaged as a
function-shaped representative producer.  This is a choice step, not a new
mathematical assumption. -/
theorem representativeProducer_of_evenNoObstructionRange
    (A : SpectralExponentCodeAdapter)
    (hno : SpectralExponentEvenNoObstructionSurjective A) :
    Nonempty (SpectralEvenNoObstructionRepresentativeProducer A) := by
  classical
  let pick :
      (n : ℕ) -> 2 ≤ n -> H1SpectralProjection (1 / 2 : ℝ) :=
    fun n hn => Classical.choose (hno n hn)
  have hspec :
      ∀ (n : ℕ) (hn : 2 ≤ n),
        A.code (pick n hn) = 2 * n ∧
          H1SpectralNoObstructionComplete (pick n hn) := by
    intro n hn
    exact Classical.choose_spec (hno n hn)
  exact
    ⟨{
      pick := pick
      code_pick := fun n hn => (hspec n hn).1
      no_obstruction_pick := fun n hn => (hspec n hn).2
    }⟩

/-- THEOREM 3: P672's concrete representative producer is exactly P671's
no-obstruction range predicate. -/
theorem representativeProducer_iff_evenNoObstructionRange
    (A : SpectralExponentCodeAdapter) :
    Nonempty (SpectralEvenNoObstructionRepresentativeProducer A) ↔
      SpectralExponentEvenNoObstructionSurjective A := by
  constructor
  · rintro ⟨P⟩
    exact evenNoObstructionRange_of_representativeProducer A P
  · exact representativeProducer_of_evenNoObstructionRange A

/-- THEOREM 4: an actual representative producer proves ordinary even
Goldbach through the adapter compatibility field. -/
theorem evenGoldbach_of_representativeProducer
    (A : SpectralExponentCodeAdapter)
    (hP : Nonempty (SpectralEvenNoObstructionRepresentativeProducer A)) :
    EvenGoldbachStatement := by
  exact
    evenGoldbach_of_adapterEvenNoObstructionSurjective A
      ((representativeProducer_iff_evenNoObstructionRange A).mp hP)

/-- THEOREM 5: a concrete representative producer is exactly adapter even
range plus ordinary even Goldbach. -/
theorem representativeProducer_iff_evenCodeRange_and_goldbach
    (A : SpectralExponentCodeAdapter) :
    Nonempty (SpectralEvenNoObstructionRepresentativeProducer A) ↔
      SpectralExponentEvenCodeSurjective A ∧ EvenGoldbachStatement := by
  exact
    (representativeProducer_iff_evenNoObstructionRange A).trans
      (adapterEvenNoObstructionSurjective_iff_evenCodeSurjective_and_goldbach A)

/-- THEOREM 6: once the adapter covers every even code, ordinary even Goldbach
is exactly the existence of a concrete no-obstructed representative producer.
-/
theorem evenGoldbach_iff_representativeProducer_of_evenCodeSurjective
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentEvenCodeSurjective A) :
    EvenGoldbachStatement ↔
      Nonempty (SpectralEvenNoObstructionRepresentativeProducer A) := by
  exact
    (evenGoldbach_iff_adapterEvenNoObstructionSurjective_of_evenCodeSurjective
      A hrange).trans
      (representativeProducer_iff_evenNoObstructionRange A).symm

/-- THEOREM 7: under even-code range, the concrete representative producer is
equivalent to coded-descent liftable H¹ no-obstruction. -/
theorem representativeProducer_iff_codedDescentLiftableH1_of_evenCodeSurjective
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentEvenCodeSurjective A) :
    Nonempty (SpectralEvenNoObstructionRepresentativeProducer A) ↔
      CodedDescentEvenLiftableH1NoObstruction A := by
  exact
    (representativeProducer_iff_evenNoObstructionRange A).trans
      (adapterEvenNoObstructionSurjective_iff_codedDescentLiftableH1_of_evenCodeSurjective
        A hrange)

/-! ## Packaged producer boundary -/

/-- The P672 certificate: the final adapter-side producer debt has a concrete
function interface, and that interface is equivalent to P671's range predicate,
ordinary Goldbach under even range, and coded-descent liftable H¹ under even
range. -/
structure AdapterRepresentativeProducerBoundaryCertificate where
  p671_boundary :
    AdapterEvenNoObstructionRangeBoundaryCertificate
  representative_producer :
    SpectralExponentCodeAdapter -> Type
  producer_iff_no_obstruction_range :
    ∀ A : SpectralExponentCodeAdapter,
      Nonempty (representative_producer A) ↔
        SpectralExponentEvenNoObstructionSurjective A
  producer_iff_range_and_goldbach :
    ∀ A : SpectralExponentCodeAdapter,
      Nonempty (representative_producer A) ↔
        SpectralExponentEvenCodeSurjective A ∧ EvenGoldbachStatement
  goldbach_iff_producer_of_range :
    ∀ A : SpectralExponentCodeAdapter,
      SpectralExponentEvenCodeSurjective A ->
        (EvenGoldbachStatement ↔ Nonempty (representative_producer A))
  producer_iff_liftable_h1_of_range :
    ∀ A : SpectralExponentCodeAdapter,
      SpectralExponentEvenCodeSurjective A ->
        (Nonempty (representative_producer A) ↔
          CodedDescentEvenLiftableH1NoObstruction A)

/-- DEFINITION 2: the canonical P672 representative-producer boundary. -/
def adapterRepresentativeProducerBoundaryCertificate :
    AdapterRepresentativeProducerBoundaryCertificate where
  p671_boundary := adapterEvenNoObstructionRangeBoundaryCertificate
  representative_producer :=
    SpectralEvenNoObstructionRepresentativeProducer
  producer_iff_no_obstruction_range :=
    representativeProducer_iff_evenNoObstructionRange
  producer_iff_range_and_goldbach :=
    representativeProducer_iff_evenCodeRange_and_goldbach
  goldbach_iff_producer_of_range :=
    evenGoldbach_iff_representativeProducer_of_evenCodeSurjective
  producer_iff_liftable_h1_of_range :=
    representativeProducer_iff_codedDescentLiftableH1_of_evenCodeSurjective

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P672's function-shaped representative
producer boundary welded below P671's no-obstruction range boundary. -/
structure RepresentativeProducerUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p671_root :
    AdapterNoObstructionRangeUnifiedRootCertificate E
  representative_boundary :
    AdapterRepresentativeProducerBoundaryCertificate
  producer_iff_range_and_goldbach :
    ∀ A : SpectralExponentCodeAdapter,
      Nonempty (SpectralEvenNoObstructionRepresentativeProducer A) ↔
        SpectralExponentEvenCodeSurjective A ∧ EvenGoldbachStatement
  producer_iff_liftable_h1_of_range :
    ∀ A : SpectralExponentCodeAdapter,
      SpectralExponentEvenCodeSurjective A ->
        (Nonempty (SpectralEvenNoObstructionRepresentativeProducer A) ↔
          CodedDescentEvenLiftableH1NoObstruction A)
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 8: the current central root with the P672 concrete producer
boundary. -/
def representativeProducerUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    RepresentativeProducerUnifiedRootCertificate E where
  p671_root := adapterNoObstructionRangeUnifiedRootCertificate (E := E)
  representative_boundary := adapterRepresentativeProducerBoundaryCertificate
  producer_iff_range_and_goldbach :=
    representativeProducer_iff_evenCodeRange_and_goldbach
  producer_iff_liftable_h1_of_range :=
    representativeProducer_iff_codedDescentLiftableH1_of_evenCodeSurjective
  alpha_s_residual :=
    (adapterNoObstructionRangeUnifiedRootCertificate (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
