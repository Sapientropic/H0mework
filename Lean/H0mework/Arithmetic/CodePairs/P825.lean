import H0mework.Physics.ColorLoops.P824

/-!
# Proposition 825: no-gap as absence of permanent color holonomy

P824 names the real remaining producer:

`SU7FilteredPrimeEdgeLoopProducer`.

This file gives the "no-gap" / "permanent holonomy" formulation.  A gap at an
even fiber means every prime-edge color loop has nonzero trace, equivalently no
prime-edge loop passes the SU(7) traceless color-adjoint filter.  A permanent
color holonomy is such a gap somewhere on the even spectrum.

Lean proves:

* no permanent color holonomy is exactly the SU(7)-filtered loop producer;
* equivalently, it is exactly the P816 unit-bracket producer;
* equivalently, it is exactly the P822 fixed-point witness producer;
* a per-fiber gap forbids every fixed-point/zero-energy witness on that fiber.

Thus the "confinement forbids permanent color holonomy" route has a single
formal inhabitance target: prove no permanent color holonomy, or equivalently
produce the SU(7)-filtered prime-edge loop selector.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open ComplexityProjection
open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Trace-spectrum gaps -/

/-- A trace-spectrum gap at the even fiber `2n`: every prime-edge loop has
nonzero gauge-invariant trace. -/
def PrimeEdgeTraceSpectrumGap (n : ℕ) : Prop :=
  ∀ p q : PrimeExponent, PrimeEdgeColorLoopObstructed n p q

/-- A SU(7)-filtered point in the prime-edge trace spectrum over `2n`. -/
def SU7FilteredTraceSpectrumFiber (n : ℕ) : Prop :=
  ∃ p q : PrimeExponent,
    GrandUnification.SU7ColorAdjointRepresentationFilter
      (primeEdgeColorLoopMatrix n p q)

/-- THEOREM 1: a trace-spectrum gap is exactly absence of a SU(7)-filtered
prime-edge loop over that fiber. -/
theorem primeEdgeTraceSpectrumGap_iff_no_su7FilteredFiber
    (n : ℕ) :
    PrimeEdgeTraceSpectrumGap n ↔
      ¬ SU7FilteredTraceSpectrumFiber n := by
  constructor
  · intro hgap hfiber
    rcases hfiber with ⟨p, q, hfilter⟩
    exact hgap p q
      ((GrandUnification.su7ColorAdjointRepresentationFilter_iff_traceExact
        (primeEdgeColorLoopMatrix n p q)).mp hfilter)
  · intro hnofiber p q hexact
    exact hnofiber
      ⟨p, q,
        (GrandUnification.su7ColorAdjointRepresentationFilter_iff_traceExact
          (primeEdgeColorLoopMatrix n p q)).mpr hexact⟩

/-- No gap on the even prime-edge trace spectrum. -/
def PrimeEdgeTraceSpectrumNoGap : Prop :=
  ∀ n : ℕ, 2 ≤ n -> SU7FilteredTraceSpectrumFiber n

/-- THEOREM 2: no-gap is exactly the P824 SU(7)-filtered loop producer. -/
theorem primeEdgeTraceSpectrumNoGap_iff_su7FilteredProducer :
    PrimeEdgeTraceSpectrumNoGap ↔
      SU7FilteredPrimeEdgeLoopProducer := by
  rfl

/-! ## Permanent color holonomy -/

/-- A permanent color holonomy: some even fiber has an unavoidable nonzero
trace-spectrum gap. -/
def PermanentPrimeEdgeColorHolonomy : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ PrimeEdgeTraceSpectrumGap n

/-- THEOREM 3: permanent color holonomy is exactly failure of the SU(7)
filtered producer. -/
theorem permanentPrimeEdgeColorHolonomy_iff_not_su7FilteredProducer :
    PermanentPrimeEdgeColorHolonomy ↔
      ¬ SU7FilteredPrimeEdgeLoopProducer := by
  constructor
  · intro hperm producer
    rcases hperm with ⟨n, hn, hgap⟩
    exact (primeEdgeTraceSpectrumGap_iff_no_su7FilteredFiber n).mp hgap
      (producer n hn)
  · intro hnot
    by_contra hnoPerm
    apply hnot
    intro n hn
    by_contra hnofiber
    exact hnoPerm
      ⟨n, hn,
        (primeEdgeTraceSpectrumGap_iff_no_su7FilteredFiber n).mpr hnofiber⟩

/-- THEOREM 4: no permanent color holonomy is exactly the SU(7)-filtered loop
producer. -/
theorem noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer :
    ¬ PermanentPrimeEdgeColorHolonomy ↔
      SU7FilteredPrimeEdgeLoopProducer := by
  constructor
  · intro hno
    by_contra hnot
    exact hno
      ((permanentPrimeEdgeColorHolonomy_iff_not_su7FilteredProducer).mpr hnot)
  · intro producer hperm
    exact
      ((permanentPrimeEdgeColorHolonomy_iff_not_su7FilteredProducer).mp hperm)
        producer

/-- THEOREM 5: no permanent color holonomy is exactly the unit-bracket
producer. -/
theorem noPermanentPrimeEdgeColorHolonomy_iff_unitBracketProducer :
    ¬ PermanentPrimeEdgeColorHolonomy ↔
      ColorLoopTraceUnitBracketProducer := by
  exact noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer.trans
    su7FilteredPrimeEdgeLoopProducer_iff_unitBracketProducer

/-- THEOREM 6: no permanent color holonomy is exactly the fixed-point witness
producer. -/
theorem noPermanentPrimeEdgeColorHolonomy_iff_fixedPointProducer :
    ¬ PermanentPrimeEdgeColorHolonomy ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer := by
  exact noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer.trans
    su7FilteredPrimeEdgeLoopProducer_iff_fixedPointProducer

/-! ## Gap forbids truth-formula fixedness on that fiber -/

/-- THEOREM 7: a trace-spectrum gap on `2n` forbids every dynamical fixed-point
witness on that fiber. -/
theorem primeEdgeTraceSpectrumGap_forbids_fixedPoint
    (n : ℕ) (hgap : PrimeEdgeTraceSpectrumGap n)
    (pair : PrimeExponent × PrimeExponent) :
    ¬ goldbachDynamicalFixedPoint (2 * n) pair := by
  intro hfix
  have hsum :
      2 * n = pair.1.1 + pair.2.1 :=
    (goldbachDynamicalFixedPoint_iff_sum (2 * n) pair).mp hfix
  have hexact :
      ColorLoopTraceExact
        (primeEdgeColorLoopMatrix n pair.1 pair.2) :=
    (primeEdgeColorLoop_trace_zero_iff n pair.1 pair.2).mpr hsum
  exact hgap pair.1 pair.2 hexact

/-- THEOREM 8: a trace-spectrum gap on `2n` forbids every zero-energy witness
on that fiber. -/
theorem primeEdgeTraceSpectrumGap_forbids_zeroEnergy
    (n : ℕ) (hgap : PrimeEdgeTraceSpectrumGap n)
    (pair : PrimeExponent × PrimeExponent) :
    hamiltonianEnergyReadout (goldbachEnergyState (2 * n) pair) ≠ 0 := by
  intro hzero
  have hfix :
      goldbachDynamicalFixedPoint (2 * n) pair :=
    (goldbachDynamicalFixedPoint_iff_zeroEnergy (2 * n) pair).mpr hzero
  exact primeEdgeTraceSpectrumGap_forbids_fixedPoint n hgap pair hfix

/-- THEOREM 9: if there is no permanent color holonomy, Lean extracts the
P816 unit bracket. -/
theorem unitBracketProducer_of_noPermanentPrimeEdgeColorHolonomy
    (hno : ¬ PermanentPrimeEdgeColorHolonomy) :
    ColorLoopTraceUnitBracketProducer :=
  (noPermanentPrimeEdgeColorHolonomy_iff_unitBracketProducer).mp hno

/-- THEOREM 10: if there is no permanent color holonomy, Lean extracts the
P822 fixed-point producer. -/
theorem fixedPointProducer_of_noPermanentPrimeEdgeColorHolonomy
    (hno : ¬ PermanentPrimeEdgeColorHolonomy) :
    Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  (noPermanentPrimeEdgeColorHolonomy_iff_fixedPointProducer).mp hno

/-! ## Certificate -/

/-- P825 certificate: no-gap / permanent holonomy normal form for the
color-loop producer. -/
structure ColorLoopNoGapPermanentHolonomyCertificate : Prop where
  gap_iff_no_filtered_fiber :
    ∀ n : ℕ,
      PrimeEdgeTraceSpectrumGap n ↔
        ¬ SU7FilteredTraceSpectrumFiber n
  no_gap_iff_su7_filtered :
    PrimeEdgeTraceSpectrumNoGap ↔
      SU7FilteredPrimeEdgeLoopProducer
  permanent_iff_not_su7_filtered :
    PermanentPrimeEdgeColorHolonomy ↔
      ¬ SU7FilteredPrimeEdgeLoopProducer
  no_permanent_iff_su7_filtered :
    ¬ PermanentPrimeEdgeColorHolonomy ↔
      SU7FilteredPrimeEdgeLoopProducer
  no_permanent_iff_unit_bracket :
    ¬ PermanentPrimeEdgeColorHolonomy ↔
      ColorLoopTraceUnitBracketProducer
  no_permanent_iff_fixed_point :
    ¬ PermanentPrimeEdgeColorHolonomy ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  gap_forbids_fixed_point :
    ∀ (n : ℕ), PrimeEdgeTraceSpectrumGap n ->
      ∀ pair : PrimeExponent × PrimeExponent,
        ¬ goldbachDynamicalFixedPoint (2 * n) pair
  gap_forbids_zero_energy :
    ∀ (n : ℕ), PrimeEdgeTraceSpectrumGap n ->
      ∀ pair : PrimeExponent × PrimeExponent,
        hamiltonianEnergyReadout (goldbachEnergyState (2 * n) pair) ≠ 0
  no_permanent_extracts_unit_bracket :
    ¬ PermanentPrimeEdgeColorHolonomy ->
      ColorLoopTraceUnitBracketProducer
  no_permanent_extracts_fixed_point :
    ¬ PermanentPrimeEdgeColorHolonomy ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer

/-- THEOREM 11: canonical no-gap / permanent holonomy certificate. -/
theorem colorLoopNoGapPermanentHolonomyCertificate :
    ColorLoopNoGapPermanentHolonomyCertificate where
  gap_iff_no_filtered_fiber :=
    primeEdgeTraceSpectrumGap_iff_no_su7FilteredFiber
  no_gap_iff_su7_filtered :=
    primeEdgeTraceSpectrumNoGap_iff_su7FilteredProducer
  permanent_iff_not_su7_filtered :=
    permanentPrimeEdgeColorHolonomy_iff_not_su7FilteredProducer
  no_permanent_iff_su7_filtered :=
    noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer
  no_permanent_iff_unit_bracket :=
    noPermanentPrimeEdgeColorHolonomy_iff_unitBracketProducer
  no_permanent_iff_fixed_point :=
    noPermanentPrimeEdgeColorHolonomy_iff_fixedPointProducer
  gap_forbids_fixed_point :=
    primeEdgeTraceSpectrumGap_forbids_fixedPoint
  gap_forbids_zero_energy :=
    primeEdgeTraceSpectrumGap_forbids_zeroEnergy
  no_permanent_extracts_unit_bracket :=
    unitBracketProducer_of_noPermanentPrimeEdgeColorHolonomy
  no_permanent_extracts_fixed_point :=
    fixedPointProducer_of_noPermanentPrimeEdgeColorHolonomy

end StandardModelConstraint
end SaturationMonoid
