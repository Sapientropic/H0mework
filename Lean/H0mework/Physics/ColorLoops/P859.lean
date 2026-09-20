import H0mework.Physics.GaugeFlow.P839
import H0mework.Physics.RunningSources.P858

/-!
# Proposition 859: confinement forbids permanent color holonomy

P825 defines a permanent color holonomy as an even fiber whose prime-edge trace
spectrum has a gap.  P846 proves that residual-split confinement is equivalent
to the gauge-flow trace-zero producer.  This file composes those two facts into
the direct route requested by the main proof spine:

`confinement -> no permanent holonomy -> no gap -> unit bracket`.

The theorem is intentionally a producer route, not another alternative
definition of Goldbach/no-gap.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open SaturationMonoid.ComplexityProjection

set_option linter.defProp false

/-- Residual-split confinement produces the SU(7)-filtered loop selector. -/
theorem su7FilteredProducer_of_confinementResidualSplit
    (H : SU7ConfinementResidualSplitLaw) :
    SU7FilteredPrimeEdgeLoopProducer := by
  have htrace : SU7GaugeFlowTraceZeroProducer :=
    (gaugeFlowTraceZeroProducer_iff_confinementResidualSplitLaw).mpr H
  rcases htrace with ⟨N⟩
  exact su7FilteredPrimeEdgeLoopProducer_of_gaugeFlowNormalizer N

/-- Residual-split confinement forbids permanent prime-edge color holonomy. -/
theorem noPermanentColorHolonomy_of_confinementResidualSplit
    (H : SU7ConfinementResidualSplitLaw) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mpr
    (su7FilteredProducer_of_confinementResidualSplit H)

/-- Residual-split confinement gives no gap in every even prime-edge trace
spectrum fiber. -/
theorem traceSpectrumNoGap_of_confinementResidualSplit
    (H : SU7ConfinementResidualSplitLaw) :
    PrimeEdgeTraceSpectrumNoGap := by
  exact su7FilteredProducer_of_confinementResidualSplit H

/-- Residual-split confinement gives the unit-bracket producer. -/
theorem unitBracketProducer_of_confinementResidualSplit
    (H : SU7ConfinementResidualSplitLaw) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_noPermanentPrimeEdgeColorHolonomy
    (noPermanentColorHolonomy_of_confinementResidualSplit H)

/-- Residual-split confinement gives the fixed-point producer. -/
theorem fixedPointProducer_of_confinementResidualSplit
    (H : SU7ConfinementResidualSplitLaw) :
    Nonempty EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_noPermanentPrimeEdgeColorHolonomy
    (noPermanentColorHolonomy_of_confinementResidualSplit H)

/-- A gap is a permanent holonomy candidate over its fiber, and therefore
cannot survive under residual-split confinement. -/
theorem noTraceSpectrumGapAt_of_confinementResidualSplit
    (H : SU7ConfinementResidualSplitLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ¬ PrimeEdgeTraceSpectrumGap n := by
  intro hgap
  exact noPermanentColorHolonomy_of_confinementResidualSplit H
    ⟨n, hn, hgap⟩

/-- Under confinement, every even fiber has a SU(7)-filtered trace-zero loop. -/
theorem filteredFiber_of_confinementResidualSplit
    (H : SU7ConfinementResidualSplitLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7FilteredTraceSpectrumFiber n :=
  traceSpectrumNoGap_of_confinementResidualSplit H n hn

/-- Truth-formula readout: confinement rules out a fiber whose residual split
would forbid every fixed-point witness. -/
theorem confinement_rules_out_fixedPoint_forbidden_gap
    (H : SU7ConfinementResidualSplitLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∀ pair : PrimeExponent × PrimeExponent,
      ¬ goldbachDynamicalFixedPoint (2 * n) pair := by
  intro hall
  rcases filteredFiber_of_confinementResidualSplit H n hn with ⟨p, q, hfilter⟩
  have hexact :
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) :=
    (GrandUnification.su7ColorAdjointRepresentationFilter_iff_traceExact
      (primeEdgeColorLoopMatrix n p q)).mp hfilter
  have hsum :
      2 * n = p.1 + q.1 :=
    (primeEdgeColorLoop_trace_zero_iff n p q).mp hexact
  have hfix :
      goldbachDynamicalFixedPoint (2 * n) (p, q) :=
    (goldbachDynamicalFixedPoint_iff_sum (2 * n) (p, q)).mpr hsum
  exact hall (p, q) hfix

/-- Energy readout: confinement rules out a fiber whose residual split would
force every prime-edge energy away from zero. -/
theorem confinement_rules_out_zeroEnergy_forbidden_gap
    (H : SU7ConfinementResidualSplitLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∀ pair : PrimeExponent × PrimeExponent,
      hamiltonianEnergyReadout (goldbachEnergyState (2 * n) pair) ≠ 0 := by
  intro hall
  rcases filteredFiber_of_confinementResidualSplit H n hn with ⟨p, q, hfilter⟩
  have hexact :
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) :=
    (GrandUnification.su7ColorAdjointRepresentationFilter_iff_traceExact
      (primeEdgeColorLoopMatrix n p q)).mp hfilter
  have hsum :
      2 * n = p.1 + q.1 :=
    (primeEdgeColorLoop_trace_zero_iff n p q).mp hexact
  have hfix :
      goldbachDynamicalFixedPoint (2 * n) (p, q) :=
    (goldbachDynamicalFixedPoint_iff_sum (2 * n) (p, q)).mpr hsum
  have hzero :
      hamiltonianEnergyReadout (goldbachEnergyState (2 * n) (p, q)) = 0 :=
    (goldbachDynamicalFixedPoint_iff_zeroEnergy (2 * n) (p, q)).mp hfix
  exact hall (p, q) hzero

/-- P859 certificate: residual-split confinement is a direct producer route to
no permanent holonomy, no-gap, unit bracket, and truth-formula fixed/energy
readouts. -/
structure ConfinementResidualSplitNoPermanentHolonomyCertificate : Prop where
  su7Filtered :
    SU7ConfinementResidualSplitLaw ->
      SU7FilteredPrimeEdgeLoopProducer
  noPermanent :
    SU7ConfinementResidualSplitLaw ->
      ¬ PermanentPrimeEdgeColorHolonomy
  noGap :
    SU7ConfinementResidualSplitLaw ->
      PrimeEdgeTraceSpectrumNoGap
  unitBracket :
    SU7ConfinementResidualSplitLaw ->
      ColorLoopTraceUnitBracketProducer
  fixedPoint :
    SU7ConfinementResidualSplitLaw ->
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  noFiberGap :
    SU7ConfinementResidualSplitLaw ->
      ∀ n : ℕ, 2 ≤ n -> ¬ PrimeEdgeTraceSpectrumGap n
  filteredFiber :
    SU7ConfinementResidualSplitLaw ->
      ∀ n : ℕ, 2 ≤ n -> SU7FilteredTraceSpectrumFiber n
  rulesOutFixedForbiddenGap :
    SU7ConfinementResidualSplitLaw ->
      ∀ n : ℕ, 2 ≤ n ->
        ¬ ∀ pair : PrimeExponent × PrimeExponent,
          ¬ goldbachDynamicalFixedPoint (2 * n) pair
  rulesOutEnergyForbiddenGap :
    SU7ConfinementResidualSplitLaw ->
      ∀ n : ℕ, 2 ≤ n ->
        ¬ ∀ pair : PrimeExponent × PrimeExponent,
          hamiltonianEnergyReadout
            (goldbachEnergyState (2 * n) pair) ≠ 0

def confinementResidualSplitNoPermanentHolonomyCertificate :
    ConfinementResidualSplitNoPermanentHolonomyCertificate where
  su7Filtered := su7FilteredProducer_of_confinementResidualSplit
  noPermanent := noPermanentColorHolonomy_of_confinementResidualSplit
  noGap := traceSpectrumNoGap_of_confinementResidualSplit
  unitBracket := unitBracketProducer_of_confinementResidualSplit
  fixedPoint := fixedPointProducer_of_confinementResidualSplit
  noFiberGap := noTraceSpectrumGapAt_of_confinementResidualSplit
  filteredFiber := filteredFiber_of_confinementResidualSplit
  rulesOutFixedForbiddenGap :=
    confinement_rules_out_fixedPoint_forbidden_gap
  rulesOutEnergyForbiddenGap :=
    confinement_rules_out_zeroEnergy_forbidden_gap


end
end StandardModelConstraint
end SaturationMonoid
