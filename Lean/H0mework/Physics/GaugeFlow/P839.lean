import H0mework.Physics.GaugeFlow.P838

/-!
# Proposition 839: SU(7) gauge-flow normalizer as the color-loop producer

P838 exposed the primitive gauge-dynamics normal form as two coordinates:

* local normal form: `allowed = trace-zero`;
* global dynamics: no permanent color holonomy.

This file pushes one layer lower.  The primitive producer is a gauge-flow
normalizer: for every even prime-edge fiber it produces an actual trace-zero
normal form.  From that data Lean extracts the no-gap field, forbids permanent
color holonomy, and builds the unit-bracket/fixed-point witness itself.

So the route is no longer:

`assume no permanent holonomy -> extract witness`.

It is:

`gauge-flow trace-zero normalizer -> no permanent holonomy -> witness`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Gauge-flow trace-zero normalizer -/

/-- A SU(7) gauge-flow trace-zero normalizer.

It is a real producer object: every even fiber `2n >= 4` is assigned a
prime-edge trace-zero normal form.  This is the data-level version of
"confinement eliminates permanent color holonomy". -/
structure SU7GaugeFlowTraceZeroNormalizer where
  normalForm : (n : ℕ) -> 2 ≤ n -> TraceZeroPrimeEdgeLoop n

/-- The proposition that such a gauge-flow normalizer exists. -/
def SU7GaugeFlowTraceZeroProducer : Prop :=
  Nonempty SU7GaugeFlowTraceZeroNormalizer

/-- THEOREM 1: a gauge-flow normalizer is already a global trace-zero sector. -/
def traceZeroPrimeEdgeSector_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    TraceZeroPrimeEdgeSector where
  loop := N.normalForm

/-- THEOREM 2: a gauge-flow normalizer canonically lifts to a global SU(7)
allowed sector. -/
def su7AllowedPrimeEdgeSector_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    SU7AllowedPrimeEdgeSector where
  loop := fun n hn =>
    su7AllowedPrimeEdgeLoopOfTraceZero (N.normalForm n hn)

/-- THEOREM 3: the normalizer lands in the trace-zero fiber on every even
prime-edge sector. -/
theorem gaugeFlowNormalizer_trace_zero
    (N : SU7GaugeFlowTraceZeroNormalizer)
    (n : ℕ) (hn : 2 ≤ n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        (N.normalForm n hn).leftPrime
        (N.normalForm n hn).rightPrime) :=
  (N.normalForm n hn).trace_zero

/-- THEOREM 4: the normalizer yields the SU(7)-filtered prime-edge loop
producer, without assuming no-permanent-holonomy as input. -/
theorem su7FilteredPrimeEdgeLoopProducer_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    SU7FilteredPrimeEdgeLoopProducer := by
  intro n hn
  refine ⟨(N.normalForm n hn).leftPrime,
    (N.normalForm n hn).rightPrime, ?_⟩
  exact
    (su7ColorAdjointRepresentationFilter_iff_traceExact
      (primeEdgeColorLoopMatrix n
        (N.normalForm n hn).leftPrime
        (N.normalForm n hn).rightPrime)).mpr
      (gaugeFlowNormalizer_trace_zero N n hn)

/-- THEOREM 5: the normalizer proves trace-spectrum no-gap. -/
theorem primeEdgeTraceSpectrumNoGap_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    PrimeEdgeTraceSpectrumNoGap :=
  (primeEdgeTraceSpectrumNoGap_iff_su7FilteredProducer).mpr
    (su7FilteredPrimeEdgeLoopProducer_of_gaugeFlowNormalizer N)

/-- THEOREM 6: the normalizer forbids permanent prime-edge color holonomy. -/
theorem noPermanentColorHolonomy_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mpr
    (su7FilteredPrimeEdgeLoopProducer_of_gaugeFlowNormalizer N)

/-- THEOREM 7: the normalizer induces the P838 primitive gauge-dynamics normal
form law. -/
theorem primitiveGaugeDynamics_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    SU7PrimitiveGaugeDynamicsNormalFormLaw where
  filter_iff_trace_zero :=
    su7ColorAdjointRepresentationFilter_iff_traceExact
  no_permanent_color_holonomy :=
    noPermanentColorHolonomy_of_gaugeFlowNormalizer N

/-- THEOREM 8: the normalizer induces the residual-split confinement law. -/
theorem confinementResidualSplitLaw_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_primitiveGaugeDynamics
    (primitiveGaugeDynamics_of_gaugeFlowNormalizer N)

/-! ## Direct witness extraction -/

/-- THEOREM 9: the gauge-flow normalizer builds the data-level color-loop
unit-bracket/fixed-point witness itself. -/
def colorLoopWitnessOfGaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    ColorLoopUnitBracketFixedPointWitness where
  pick := fun n hn =>
    ((N.normalForm n hn).leftPrime, (N.normalForm n hn).rightPrime)
  trace_exact := by
    intro n hn
    exact gaugeFlowNormalizer_trace_zero N n hn
  unit_bracket := by
    intro n hn
    exact
      colorLoopTraceUnitBracket_of_traceExact n
        (N.normalForm n hn).leftPrime
        (N.normalForm n hn).rightPrime
        (gaugeFlowNormalizer_trace_zero N n hn)
  fixed := by
    intro n hn
    exact
      goldbachDynamicalFixedPoint_of_traceExact n
        (N.normalForm n hn).leftPrime
        (N.normalForm n hn).rightPrime
        (gaugeFlowNormalizer_trace_zero N n hn)

/-- THEOREM 10: the normalizer produces the unit bracket. -/
theorem unitBracketProducer_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducerOfColorLoopWitness
    (colorLoopWitnessOfGaugeFlowNormalizer N)

/-- THEOREM 11: the normalizer produces the fixed-point producer. -/
def fixedPointProducer_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducerOfColorLoopWitness
    (colorLoopWitnessOfGaugeFlowNormalizer N)

/-- THEOREM 12: the normalizer produces the spectrum-resolved alpha convergent
carrier through P838. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    SpectrumResolvedAlphaConvergentCarrier :=
  spectrumResolvedAlphaConvergentCarrier_of_primitiveGaugeDynamics
    (primitiveGaugeDynamics_of_gaugeFlowNormalizer N)

/-- THEOREM 13: the normalizer produces the alpha strong convergent carrier
nail. -/
theorem alphaStrongConvergentCarrierNail_of_gaugeFlowNormalizer
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    GrandUnification.AlphaStrongConvergentCarrierNail :=
  alphaStrongConvergentCarrierNail_of_primitiveGaugeDynamics
    (primitiveGaugeDynamics_of_gaugeFlowNormalizer N)

/-! ## Producer-level readouts -/

/-- THEOREM 14: existence of a gauge-flow normalizer forbids permanent color
holonomy. -/
theorem noPermanentColorHolonomy_of_gaugeFlowTraceZeroProducer
    (H : SU7GaugeFlowTraceZeroProducer) :
    ¬ PermanentPrimeEdgeColorHolonomy := by
  rcases H with ⟨N⟩
  exact noPermanentColorHolonomy_of_gaugeFlowNormalizer N

/-- THEOREM 15: existence of a gauge-flow normalizer induces primitive gauge
dynamics. -/
theorem primitiveGaugeDynamics_of_gaugeFlowTraceZeroProducer
    (H : SU7GaugeFlowTraceZeroProducer) :
    SU7PrimitiveGaugeDynamicsNormalFormLaw := by
  rcases H with ⟨N⟩
  exact primitiveGaugeDynamics_of_gaugeFlowNormalizer N

/-- THEOREM 16: existence of a gauge-flow normalizer produces the color-loop
witness. -/
def colorLoopWitnessOfGaugeFlowTraceZeroProducer
    (H : SU7GaugeFlowTraceZeroProducer) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitnessOfGaugeFlowNormalizer (Classical.choice H)

/-- THEOREM 17: existence of a gauge-flow normalizer produces the fixed-point
producer. -/
def fixedPointProducer_of_gaugeFlowTraceZeroProducer
    (H : SU7GaugeFlowTraceZeroProducer) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_gaugeFlowNormalizer (Classical.choice H)

/-! ## Certificate -/

/-- P839 certificate: the gauge-flow trace-zero normalizer is the direct
producer under the primitive no-permanent-holonomy field. -/
structure SU7GaugeFlowTraceZeroNormalizerCertificate where
  normalizer_to_trace_zero_sector :
    SU7GaugeFlowTraceZeroNormalizer -> TraceZeroPrimeEdgeSector
  normalizer_to_allowed_sector :
    SU7GaugeFlowTraceZeroNormalizer -> SU7AllowedPrimeEdgeSector
  normalizer_trace_zero :
    ∀ (N : SU7GaugeFlowTraceZeroNormalizer)
      (n : ℕ) (hn : 2 ≤ n),
      ColorLoopTraceExact
        (primeEdgeColorLoopMatrix n
          (N.normalForm n hn).leftPrime
          (N.normalForm n hn).rightPrime)
  normalizer_to_filtered_producer :
    SU7GaugeFlowTraceZeroNormalizer -> SU7FilteredPrimeEdgeLoopProducer
  normalizer_to_no_gap :
    SU7GaugeFlowTraceZeroNormalizer -> PrimeEdgeTraceSpectrumNoGap
  normalizer_to_no_permanent :
    SU7GaugeFlowTraceZeroNormalizer -> ¬ PermanentPrimeEdgeColorHolonomy
  normalizer_to_primitive :
    SU7GaugeFlowTraceZeroNormalizer ->
      SU7PrimitiveGaugeDynamicsNormalFormLaw
  normalizer_to_confinement :
    SU7GaugeFlowTraceZeroNormalizer -> SU7ConfinementResidualSplitLaw
  normalizer_to_witness :
    SU7GaugeFlowTraceZeroNormalizer ->
      ColorLoopUnitBracketFixedPointWitness
  normalizer_to_unit_bracket :
    SU7GaugeFlowTraceZeroNormalizer -> ColorLoopTraceUnitBracketProducer
  normalizer_to_fixed_point :
    SU7GaugeFlowTraceZeroNormalizer ->
      EvenGoldbachDynamicalFixedPointProducer
  producer_to_no_permanent :
    SU7GaugeFlowTraceZeroProducer -> ¬ PermanentPrimeEdgeColorHolonomy
  producer_to_primitive :
    SU7GaugeFlowTraceZeroProducer ->
      SU7PrimitiveGaugeDynamicsNormalFormLaw
  producer_to_witness :
    SU7GaugeFlowTraceZeroProducer ->
      ColorLoopUnitBracketFixedPointWitness

/-- THEOREM 18: canonical P839 gauge-flow trace-zero normalizer certificate. -/
def su7GaugeFlowTraceZeroNormalizerCertificate :
    SU7GaugeFlowTraceZeroNormalizerCertificate where
  normalizer_to_trace_zero_sector :=
    traceZeroPrimeEdgeSector_of_gaugeFlowNormalizer
  normalizer_to_allowed_sector :=
    su7AllowedPrimeEdgeSector_of_gaugeFlowNormalizer
  normalizer_trace_zero :=
    gaugeFlowNormalizer_trace_zero
  normalizer_to_filtered_producer :=
    su7FilteredPrimeEdgeLoopProducer_of_gaugeFlowNormalizer
  normalizer_to_no_gap :=
    primeEdgeTraceSpectrumNoGap_of_gaugeFlowNormalizer
  normalizer_to_no_permanent :=
    noPermanentColorHolonomy_of_gaugeFlowNormalizer
  normalizer_to_primitive :=
    primitiveGaugeDynamics_of_gaugeFlowNormalizer
  normalizer_to_confinement :=
    confinementResidualSplitLaw_of_gaugeFlowNormalizer
  normalizer_to_witness :=
    colorLoopWitnessOfGaugeFlowNormalizer
  normalizer_to_unit_bracket :=
    unitBracketProducer_of_gaugeFlowNormalizer
  normalizer_to_fixed_point :=
    fixedPointProducer_of_gaugeFlowNormalizer
  producer_to_no_permanent :=
    noPermanentColorHolonomy_of_gaugeFlowTraceZeroProducer
  producer_to_primitive :=
    primitiveGaugeDynamics_of_gaugeFlowTraceZeroProducer
  producer_to_witness :=
    colorLoopWitnessOfGaugeFlowTraceZeroProducer


end StandardModelConstraint
end SaturationMonoid
