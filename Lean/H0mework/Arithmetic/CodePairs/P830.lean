import H0mework.Physics.BranchSources.P827

/-!
# Proposition 830: the color-loop unit bracket / fixed-point witness itself

P827 lowered the remaining color-loop producer to a concrete confinement
selector.  This file removes one more layer of indirection: it defines the
actual data-level witness carried by that selector.

The same prime-edge `pick` now carries all three readings at once:

* trace-exact color loop;
* degenerate unit bracket at the zero endpoint;
* dynamical fixed point of the half-rate residual transport.

So the object produced here is not another carrier-consistency shell.  It is
the unit-bracket / fixed-point witness itself.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation
open GrandUnification

/-! ## Local conversion: trace exactness produces bracket and fixedness -/

/-- A trace-exact prime-edge loop gives the degenerate unit bracket whose two
endpoints are the same zero-trace prime pair. -/
theorem colorLoopTraceUnitBracket_of_traceExact
    (n : ℕ) (p q : PrimeExponent)
    (htrace :
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q)) :
    ColorLoopTraceUnitBracket n p q p q := by
  have hsum :
      2 * n = p.1 + q.1 :=
    (primeEdgeColorLoop_trace_zero_iff n p q).mp htrace
  have hzero :
      colorLoopTraceDefectInt n p q = 0 :=
    (colorLoopTraceDefectInt_zero_iff_goldbach_pair n p q).mpr hsum
  simp [ColorLoopTraceUnitBracket, hzero]

/-- The same trace-exact prime-edge loop is a fixed point of the canonical
Goldbach half-rate residual transport. -/
theorem goldbachDynamicalFixedPoint_of_traceExact
    (n : ℕ) (p q : PrimeExponent)
    (htrace :
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q)) :
    goldbachDynamicalFixedPoint (2 * n) (p, q) := by
  exact
    (goldbachDynamicalFixedPoint_iff_sum (2 * n) (p, q)).mpr
      ((primeEdgeColorLoop_trace_zero_iff n p q).mp htrace)

/-! ## The witness object -/

/-- A data-level color-loop witness: for every even fiber `2n >= 4`, the same
selected prime-edge pair gives trace exactness, the unit bracket, and the
fixed point. -/
structure ColorLoopUnitBracketFixedPointWitness where
  pick : (n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent
  trace_exact :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      ColorLoopTraceExact
        (primeEdgeColorLoopMatrix n (pick n hn).1 (pick n hn).2)
  unit_bracket :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      ColorLoopTraceUnitBracket
        n (pick n hn).1 (pick n hn).2
          (pick n hn).1 (pick n hn).2
  fixed :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      goldbachDynamicalFixedPoint (2 * n) (pick n hn)

/-- THEOREM 1: the witness's selected pair sums to the even target. -/
theorem colorLoopUnitBracketFixedPointWitness_sum
    (W : ColorLoopUnitBracketFixedPointWitness)
    (n : ℕ) (hn : 2 ≤ n) :
    2 * n = (W.pick n hn).1.1 + (W.pick n hn).2.1 :=
  (primeEdgeColorLoop_trace_zero_iff
    n (W.pick n hn).1 (W.pick n hn).2).mp
      (W.trace_exact n hn)

/-- THEOREM 2: a witness directly produces ordinary prime-pair witnesses. -/
def primePairProducerOfColorLoopWitness
    (W : ColorLoopUnitBracketFixedPointWitness) :
    EvenGoldbachPrimePairProducer where
  pick := W.pick
  sum_pick := colorLoopUnitBracketFixedPointWitness_sum W

/-- THEOREM 3: a witness directly produces the unit-bracket producer. -/
theorem unitBracketProducerOfColorLoopWitness
    (W : ColorLoopUnitBracketFixedPointWitness) :
    ColorLoopTraceUnitBracketProducer := by
  intro n hn
  exact ⟨(W.pick n hn).1, (W.pick n hn).2,
    (W.pick n hn).1, (W.pick n hn).2, W.unit_bracket n hn⟩

/-- THEOREM 4: a witness directly produces the fixed-point producer. -/
def fixedPointProducerOfColorLoopWitness
    (W : ColorLoopUnitBracketFixedPointWitness) :
    EvenGoldbachDynamicalFixedPointProducer where
  pick := W.pick
  fixed := W.fixed

/-- THEOREM 5: a witness directly reconstructs the SU(7) confinement selector,
because trace-exactness is the same SU(7) color-adjoint/traceless filter. -/
def confinementSelectorOfColorLoopWitness
    (W : ColorLoopUnitBracketFixedPointWitness) :
    SU7ConfinementPrimeEdgeSelector where
  pick := W.pick
  filtered := by
    intro n hn
    exact
      (su7ColorAdjointRepresentationFilter_iff_traceExact
        (primeEdgeColorLoopMatrix n (W.pick n hn).1 (W.pick n hn).2)).mpr
        (W.trace_exact n hn)

/-! ## Producing the witness from the SU(7) confinement selector -/

/-- THEOREM 6: a SU(7) confinement selector produces the unit-bracket /
fixed-point witness itself. -/
def colorLoopUnitBracketFixedPointWitnessOfConfinementSelector
    (S : SU7ConfinementPrimeEdgeSelector) :
    ColorLoopUnitBracketFixedPointWitness where
  pick := S.pick
  trace_exact := by
    intro n hn
    exact
      (su7ColorAdjointRepresentationFilter_iff_traceExact
        (primeEdgeColorLoopMatrix n (S.pick n hn).1 (S.pick n hn).2)).mp
        (S.filtered n hn)
  unit_bracket := by
    intro n hn
    exact
      colorLoopTraceUnitBracket_of_traceExact
        n (S.pick n hn).1 (S.pick n hn).2
        ((su7ColorAdjointRepresentationFilter_iff_traceExact
          (primeEdgeColorLoopMatrix n (S.pick n hn).1 (S.pick n hn).2)).mp
          (S.filtered n hn))
  fixed := by
    intro n hn
    exact
      goldbachDynamicalFixedPoint_of_traceExact
        n (S.pick n hn).1 (S.pick n hn).2
        ((su7ColorAdjointRepresentationFilter_iff_traceExact
          (primeEdgeColorLoopMatrix n (S.pick n hn).1 (S.pick n hn).2)).mp
          (S.filtered n hn))

/-- THEOREM 7: the witness produced from a selector has the same selected
pairs as the selector. -/
theorem colorLoopWitnessOfConfinementSelector_pick_eq
    (S : SU7ConfinementPrimeEdgeSelector)
    (n : ℕ) (hn : 2 ≤ n) :
    (colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S).pick n hn =
      S.pick n hn := rfl

/-- THEOREM 8: the witness object is equivalent to the selector object at the
inhabitance level. -/
theorem nonemptyColorLoopWitness_iff_confinementSelector :
    Nonempty ColorLoopUnitBracketFixedPointWitness ↔
      Nonempty SU7ConfinementPrimeEdgeSelector := by
  constructor
  · rintro ⟨W⟩
    exact ⟨confinementSelectorOfColorLoopWitness W⟩
  · rintro ⟨S⟩
    exact ⟨colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S⟩

/-- Build the unified witness from a unit-bracket producer by extracting its
prime-pair selector and using the zero endpoint as the degenerate bracket. -/
def colorLoopWitnessOfUnitBracketProducer
    (P : ColorLoopTraceUnitBracketProducer) :
    ColorLoopUnitBracketFixedPointWitness where
  pick := (primePairProducerOfUnitBracket P).pick
  trace_exact := by
    intro n hn
    exact
      (primeEdgeColorLoop_trace_zero_iff
        n ((primePairProducerOfUnitBracket P).pick n hn).1
          ((primePairProducerOfUnitBracket P).pick n hn).2).mpr
        (primePairProducerOfUnitBracket_sum P n hn)
  unit_bracket := by
    intro n hn
    exact
      colorLoopTraceUnitBracket_of_traceExact
        n ((primePairProducerOfUnitBracket P).pick n hn).1
          ((primePairProducerOfUnitBracket P).pick n hn).2
        ((primeEdgeColorLoop_trace_zero_iff
          n ((primePairProducerOfUnitBracket P).pick n hn).1
            ((primePairProducerOfUnitBracket P).pick n hn).2).mpr
          (primePairProducerOfUnitBracket_sum P n hn))
  fixed := by
    intro n hn
    exact
      goldbachDynamicalFixedPoint_of_traceExact
        n ((primePairProducerOfUnitBracket P).pick n hn).1
          ((primePairProducerOfUnitBracket P).pick n hn).2
        ((primeEdgeColorLoop_trace_zero_iff
          n ((primePairProducerOfUnitBracket P).pick n hn).1
            ((primePairProducerOfUnitBracket P).pick n hn).2).mpr
          (primePairProducerOfUnitBracket_sum P n hn))

/-- Build the unified witness from a fixed-point producer by reading fixedness
as the zero trace / prime-pair sum. -/
def colorLoopWitnessOfFixedPointProducer
    (P : EvenGoldbachDynamicalFixedPointProducer) :
    ColorLoopUnitBracketFixedPointWitness where
  pick := P.pick
  trace_exact := by
    intro n hn
    exact
      (primeEdgeColorLoop_trace_zero_iff
        n (P.pick n hn).1 (P.pick n hn).2).mpr
        ((goldbachDynamicalFixedPoint_iff_sum
          (2 * n) (P.pick n hn)).mp (P.fixed n hn))
  unit_bracket := by
    intro n hn
    exact
      colorLoopTraceUnitBracket_of_traceExact
        n (P.pick n hn).1 (P.pick n hn).2
        ((primeEdgeColorLoop_trace_zero_iff
          n (P.pick n hn).1 (P.pick n hn).2).mpr
          ((goldbachDynamicalFixedPoint_iff_sum
            (2 * n) (P.pick n hn)).mp (P.fixed n hn)))
  fixed := P.fixed

/-- THEOREM 9: the witness object is equivalent to the unit-bracket producer. -/
theorem nonemptyColorLoopWitness_iff_unitBracketProducer :
    Nonempty ColorLoopUnitBracketFixedPointWitness ↔
      ColorLoopTraceUnitBracketProducer := by
  constructor
  · rintro ⟨W⟩
    exact unitBracketProducerOfColorLoopWitness W
  · intro P
    exact ⟨colorLoopWitnessOfUnitBracketProducer P⟩

/-- THEOREM 10: the witness object is equivalent to the fixed-point producer. -/
theorem nonemptyColorLoopWitness_iff_fixedPointProducer :
    Nonempty ColorLoopUnitBracketFixedPointWitness ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer := by
  constructor
  · rintro ⟨W⟩
    exact ⟨fixedPointProducerOfColorLoopWitness W⟩
  · rintro ⟨P⟩
    exact ⟨colorLoopWitnessOfFixedPointProducer P⟩

/-- THEOREM 11: extracting the unit-bracket producer from the produced witness
gives a direct unit-bracket producer. -/
theorem unitBracketProducer_of_confinementSelector_via_witness
    (S : SU7ConfinementPrimeEdgeSelector) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducerOfColorLoopWitness
    (colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S)

/-- THEOREM 12: extracting the fixed-point producer from the produced witness
gives a direct fixed-point producer. -/
def fixedPointProducerOfConfinementSelector_via_witness
    (S : SU7ConfinementPrimeEdgeSelector) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducerOfColorLoopWitness
    (colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S)

/-- Compact certificate: the color-loop witness itself is produced from a
SU(7) confinement selector and directly yields unit-bracket and fixed-point
producers using the same selected prime-edge pairs. -/
structure ColorLoopUnitBracketFixedPointWitnessCertificate : Prop where
  witness_iff_selector :
    Nonempty ColorLoopUnitBracketFixedPointWitness ↔
      Nonempty SU7ConfinementPrimeEdgeSelector
  witness_iff_unit_bracket :
    Nonempty ColorLoopUnitBracketFixedPointWitness ↔
      ColorLoopTraceUnitBracketProducer
  witness_iff_fixed_point :
    Nonempty ColorLoopUnitBracketFixedPointWitness ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  selector_witness_sums :
    ∀ (S : SU7ConfinementPrimeEdgeSelector) (n : ℕ) (hn : 2 ≤ n),
      2 * n =
        ((colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S).pick
          n hn).1.1 +
        ((colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S).pick
          n hn).2.1
  selector_witness_unit_bracket :
    SU7ConfinementPrimeEdgeSelector -> ColorLoopTraceUnitBracketProducer
  selector_witness_fixed_point :
    SU7ConfinementPrimeEdgeSelector ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  selector_witness_same_pick :
    ∀ (S : SU7ConfinementPrimeEdgeSelector) (n : ℕ) (hn : 2 ≤ n),
      (colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S).pick n hn =
        S.pick n hn

/-- THEOREM 9: canonical witness certificate. -/
theorem colorLoopUnitBracketFixedPointWitnessCertificate :
    ColorLoopUnitBracketFixedPointWitnessCertificate where
  witness_iff_selector :=
    nonemptyColorLoopWitness_iff_confinementSelector
  witness_iff_unit_bracket :=
    nonemptyColorLoopWitness_iff_unitBracketProducer
  witness_iff_fixed_point :=
    nonemptyColorLoopWitness_iff_fixedPointProducer
  selector_witness_sums := by
    intro S n hn
    exact colorLoopUnitBracketFixedPointWitness_sum
      (colorLoopUnitBracketFixedPointWitnessOfConfinementSelector S) n hn
  selector_witness_unit_bracket := by
    intro S
    exact unitBracketProducer_of_confinementSelector_via_witness S
  selector_witness_fixed_point := by
    intro S
    exact ⟨fixedPointProducerOfConfinementSelector_via_witness S⟩
  selector_witness_same_pick := by
    intro S n hn
    rfl

end StandardModelConstraint
end SaturationMonoid
