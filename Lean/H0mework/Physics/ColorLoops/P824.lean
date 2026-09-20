import H0mework.Arithmetic.PrimeShadow.P819
import H0mework.Physics.ColorLoops.P822

/-!
# Proposition 824: SU(7)-filtered color-loop producer normal form

P818 proves that the SU(7) color-adjoint filter is the trace-zero fiber of the
P348 color-loop observable.  P822 proves that the remaining color-loop producer
is exactly an explicit prime-pair / fixed-point producer.

This file welds those two facts without adding another consistency shell.
The actual object to produce is now named:

`SU7FilteredPrimeEdgeLoopProducer`.

It must choose, for every even fiber `2n >= 4`, a prime-edge loop that passes
the SU(7) traceless color-adjoint filter.  Lean proves this is exactly the
unit-bracket producer and exactly the fixed-point witness producer.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## The SU(7)-filtered producer itself -/

/-- A global producer that chooses, for every even exponent `2n >= 4`, a
prime-edge loop passing the SU(7) traceless color-adjoint filter. -/
def SU7FilteredPrimeEdgeLoopProducer : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ p q : PrimeExponent,
      GrandUnification.SU7ColorAdjointRepresentationFilter
        (primeEdgeColorLoopMatrix n p q)

/-- THEOREM 1: producing SU(7)-filtered prime-edge loops is exactly producing
trace-exact prime-edge loops. -/
theorem su7FilteredPrimeEdgeLoopProducer_iff_traceExactProducer :
    SU7FilteredPrimeEdgeLoopProducer ↔
      ColorLoopTraceExactPrimePairProducer := by
  constructor
  · intro producer n hn
    rcases producer n hn with ⟨p, q, hfilter⟩
    exact ⟨p, q,
      (GrandUnification.su7ColorAdjointRepresentationFilter_iff_traceExact
        (primeEdgeColorLoopMatrix n p q)).mp hfilter⟩
  · intro producer n hn
    rcases producer n hn with ⟨p, q, hexact⟩
    exact ⟨p, q,
      (GrandUnification.su7ColorAdjointRepresentationFilter_iff_traceExact
        (primeEdgeColorLoopMatrix n p q)).mpr hexact⟩

/-- THEOREM 2: producing SU(7)-filtered prime-edge loops is exactly ordinary
even Goldbach. -/
theorem su7FilteredPrimeEdgeLoopProducer_iff_evenGoldbach :
    SU7FilteredPrimeEdgeLoopProducer ↔
      EvenGoldbachStatement := by
  exact su7FilteredPrimeEdgeLoopProducer_iff_traceExactProducer.trans
    colorLoopTraceExactProducer_iff_evenGoldbach

/-- THEOREM 3: the SU(7)-filtered loop producer is exactly the P816 unit
bracket producer. -/
theorem su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer :
    SU7FilteredPrimeEdgeLoopProducer ↔
      ColorLoopTraceUnitBracketProducer := by
  rw [su7FilteredPrimeEdgeLoopProducer_iff_evenGoldbach,
    colorLoopTraceUnitBracketProducer_iff_evenGoldbach]

/-- THEOREM 4: the SU(7)-filtered loop producer is exactly the P822 certified
fixed-point witness producer. -/
theorem su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer :
    SU7FilteredPrimeEdgeLoopProducer ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer := by
  exact su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer.trans
    colorLoopTraceUnitBracketProducer_iff_fixedPointProducer

/-! ## Extracting the witnesses -/

/-- Extract the P816 unit-bracket producer from a SU(7)-filtered loop
producer. -/
noncomputable def unitBracketProducerOfSU7FilteredLoopProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    ColorLoopTraceUnitBracketProducer :=
  (su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer).mp P

/-- Extract the certified fixed-point producer from a SU(7)-filtered loop
producer. -/
noncomputable def fixedPointProducerOfSU7FilteredLoopProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    EvenGoldbachDynamicalFixedPointProducer :=
  Classical.choice
    ((su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer).mp P)

/-- THEOREM 5: the unit-bracket producer extracted from a SU(7)-filtered loop
producer supplies a prime-pair zero endpoint for every even fiber. -/
theorem su7FilteredLoopProducer_extractedPrimePair_sum
    (P : SU7FilteredPrimeEdgeLoopProducer)
    (n : ℕ) (hn : 2 ≤ n) :
    2 * n =
      ((primePairProducerOfUnitBracket
        (unitBracketProducerOfSU7FilteredLoopProducer P)).pick n hn).1.1 +
        ((primePairProducerOfUnitBracket
          (unitBracketProducerOfSU7FilteredLoopProducer P)).pick n hn).2.1 := by
  exact
    primePairProducerOfUnitBracket_sum
      (unitBracketProducerOfSU7FilteredLoopProducer P) n hn

/-- THEOREM 6: the fixed-point producer extracted from a SU(7)-filtered loop
producer is fixed at every even fiber. -/
theorem su7FilteredLoopProducer_extractedFixedPoint_fixed
    (P : SU7FilteredPrimeEdgeLoopProducer)
    (n : ℕ) (hn : 2 ≤ n) :
    goldbachDynamicalFixedPoint (2 * n)
      ((fixedPointProducerOfSU7FilteredLoopProducer P).pick n hn) := by
  exact (fixedPointProducerOfSU7FilteredLoopProducer P).fixed n hn

/-- THEOREM 7: any SU(7)-filtered producer excludes permanent nonzero-trace
color holonomy on every produced even fiber. -/
theorem noPermanentColorHolonomy_of_su7FilteredLoopProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    ¬ GrandUnification.PermanentGoldbachGaugeObstruction := by
  exact
    GrandUnification.noPermanentGaugeObstruction_of_alphaStrongConvergentCarrierNail
      { exact_inverse_residual :=
          GrandUnification.alphaStrongExactInverseResidualNail
        fixed_point_convergence :=
          (su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer).mp P }

/-! ## Certificate -/

/-- P824 certificate: the SU(7)-filtered prime-edge loop producer is exactly
the unit-bracket / fixed-point witness producer. -/
structure SU7FilteredColorLoopProducerNormalFormCertificate : Prop where
  filtered_iff_trace_exact :
    SU7FilteredPrimeEdgeLoopProducer ↔
      ColorLoopTraceExactPrimePairProducer
  filtered_iff_goldbach :
    SU7FilteredPrimeEdgeLoopProducer ↔
      EvenGoldbachStatement
  filtered_iff_unit_bracket :
    SU7FilteredPrimeEdgeLoopProducer ↔
      ColorLoopTraceUnitBracketProducer
  filtered_iff_fixed_point :
    SU7FilteredPrimeEdgeLoopProducer ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  extracted_prime_pair_sums :
    ∀ (P : SU7FilteredPrimeEdgeLoopProducer) (n : ℕ) (hn : 2 ≤ n),
      2 * n =
        ((primePairProducerOfUnitBracket
          (unitBracketProducerOfSU7FilteredLoopProducer P)).pick n hn).1.1 +
          ((primePairProducerOfUnitBracket
            (unitBracketProducerOfSU7FilteredLoopProducer P)).pick n hn).2.1
  extracted_fixed_point :
    ∀ (P : SU7FilteredPrimeEdgeLoopProducer) (n : ℕ) (hn : 2 ≤ n),
      goldbachDynamicalFixedPoint (2 * n)
        ((fixedPointProducerOfSU7FilteredLoopProducer P).pick n hn)
  no_permanent_color_holonomy :
    SU7FilteredPrimeEdgeLoopProducer ->
      ¬ GrandUnification.PermanentGoldbachGaugeObstruction

/-- THEOREM 8: canonical SU(7)-filtered color-loop producer normal form. -/
theorem su7FilteredColorLoopProducerNormalFormCertificate :
    SU7FilteredColorLoopProducerNormalFormCertificate where
  filtered_iff_trace_exact :=
    su7FilteredPrimeEdgeLoopProducer_iff_traceExactProducer
  filtered_iff_goldbach :=
    su7FilteredPrimeEdgeLoopProducer_iff_evenGoldbach
  filtered_iff_unit_bracket :=
    su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer
  filtered_iff_fixed_point :=
    su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer
  extracted_prime_pair_sums :=
    su7FilteredLoopProducer_extractedPrimePair_sum
  extracted_fixed_point :=
    su7FilteredLoopProducer_extractedFixedPoint_fixed
  no_permanent_color_holonomy :=
    noPermanentColorHolonomy_of_su7FilteredLoopProducer

end StandardModelConstraint
end SaturationMonoid
