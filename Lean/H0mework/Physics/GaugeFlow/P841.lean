import H0mework.Physics.GaugeFlow.P840

/-!
# Proposition 841: SU(7) gauge-flow action zeros generate fixed points

P840 lowered the color-loop producer to a fixed-point law for active scalar
residual transport.  This file lowers it one more step to the action/energy
reading of the same truth formula.

The primitive object here is an action-zero law: for every even prime-edge
fiber, the SU(7) gauge flow chooses a prime pair whose scalar trace-defect
energy is zero.  Because P831 already proved the positive-definite energy
reading

`energy = 0 <-> residual = 0 <-> fixed`,

this action-zero law generates the P840 fixed-point law, and therefore the
trace-zero normalizer / no-gap / witness / unit-bracket / alpha-convergence
chain.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Gauge-flow action-zero law -/

/-- SU(7) gauge-flow action-zero law.

This is lower than P840's fixed-point law: it does not assert fixedness
directly.  It asserts that the selected prime-edge trace residual has zero
positive-definite scalar action/energy. -/
structure SU7GaugeFlowActionZeroLaw where
  sigma : ℝ
  sigma_active : sigma ≠ 0
  pick : (n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent
  action_zero :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      colorLoopScalarResidualEnergy
        (colorLoopTraceResidual n (pick n hn).1 (pick n hn).2) = 0

/-- The proposition that such an action-zero law exists. -/
def SU7GaugeFlowActionZeroProducer : Prop :=
  Nonempty SU7GaugeFlowActionZeroLaw

/-- THEOREM 1: zero scalar color-loop action gives zero trace residual. -/
theorem gaugeFlowActionZero_traceResidual_zero
    (A : SU7GaugeFlowActionZeroLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    colorLoopTraceResidual n (A.pick n hn).1 (A.pick n hn).2 = 0 := by
  exact
    (colorLoopScalarResidualEnergy_zero_iff
      (colorLoopTraceResidual n (A.pick n hn).1 (A.pick n hn).2)).mp
      (A.action_zero n hn)

/-- THEOREM 2: zero scalar color-loop action gives fixed residual transport. -/
theorem gaugeFlowActionZero_fixed
    (A : SU7GaugeFlowActionZeroLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ResidualTransportFixed
      (colorLoopScalarKeep A.sigma)
      (colorLoopTraceResidual n (A.pick n hn).1 (A.pick n hn).2) := by
  have hcore :=
    colorLoopResidualSplitCoreEquivalence
      A.sigma A.sigma_active n (A.pick n hn).1 (A.pick n hn).2
  exact hcore.fixed_iff_zero_energy.mpr (A.action_zero n hn)

/-- THEOREM 3: action-zero laws generate P840 fixed-point laws. -/
def gaugeFlowFixedPointLaw_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    SU7GaugeFlowFixedPointLaw where
  sigma := A.sigma
  sigma_active := A.sigma_active
  pick := A.pick
  fixed := gaugeFlowActionZero_fixed A

/-- THEOREM 4: action-zero laws generate the trace-zero normalizer. -/
def gaugeFlowTraceZeroNormalizer_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    SU7GaugeFlowTraceZeroNormalizer :=
  gaugeFlowTraceZeroNormalizer_of_fixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 5: action-zero laws prove no trace-spectrum gap. -/
theorem primeEdgeTraceSpectrumNoGap_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    PrimeEdgeTraceSpectrumNoGap :=
  primeEdgeTraceSpectrumNoGap_of_gaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 6: action-zero laws forbid permanent color holonomy. -/
theorem noPermanentColorHolonomy_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  noPermanentColorHolonomy_of_gaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 7: action-zero laws induce primitive SU(7) gauge dynamics. -/
theorem primitiveGaugeDynamics_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    SU7PrimitiveGaugeDynamicsNormalFormLaw :=
  primitiveGaugeDynamics_of_gaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 8: action-zero laws induce residual-split confinement. -/
theorem confinementResidualSplitLaw_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    SU7ConfinementResidualSplitLaw :=
  confinementResidualSplitLaw_of_gaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 9: action-zero laws build the data-level color-loop witness. -/
def colorLoopWitnessOfActionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitnessOfGaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 10: action-zero laws produce the unit bracket. -/
theorem unitBracketProducer_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_gaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 11: action-zero laws produce the fixed-point producer. -/
def fixedPointProducer_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    EvenGoldbachDynamicalFixedPointProducer :=
  fixedPointProducer_of_gaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-- THEOREM 12: action-zero laws produce the spectrum-resolved alpha
convergent carrier. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_actionZeroLaw
    (A : SU7GaugeFlowActionZeroLaw) :
    SpectrumResolvedAlphaConvergentCarrier :=
  spectrumResolvedAlphaConvergentCarrier_of_gaugeFlowFixedPointLaw
    (gaugeFlowFixedPointLaw_of_actionZeroLaw A)

/-! ## Producer-level readouts -/

/-- THEOREM 13: existence of an action-zero law produces the fixed-point law. -/
def gaugeFlowFixedPointLaw_of_actionZeroProducer
    (H : SU7GaugeFlowActionZeroProducer) :
    SU7GaugeFlowFixedPointLaw :=
  gaugeFlowFixedPointLaw_of_actionZeroLaw (Classical.choice H)

/-- THEOREM 14: existence of an action-zero law produces the trace-zero
normalizer. -/
def gaugeFlowTraceZeroNormalizer_of_actionZeroProducer
    (H : SU7GaugeFlowActionZeroProducer) :
    SU7GaugeFlowTraceZeroNormalizer :=
  gaugeFlowTraceZeroNormalizer_of_actionZeroLaw (Classical.choice H)

/-- THEOREM 15: existence of an action-zero law forbids permanent color
holonomy. -/
theorem noPermanentColorHolonomy_of_actionZeroProducer
    (H : SU7GaugeFlowActionZeroProducer) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  noPermanentColorHolonomy_of_actionZeroLaw (Classical.choice H)

/-- THEOREM 16: existence of an action-zero law produces the color-loop
witness. -/
def colorLoopWitnessOfActionZeroProducer
    (H : SU7GaugeFlowActionZeroProducer) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitnessOfActionZeroLaw (Classical.choice H)

/-! ## Certificate -/

/-- P841 certificate: action-zero gauge flow generates the P840 fixed-point
law, and therefore the full trace-zero / no-gap / witness chain. -/
structure SU7GaugeFlowActionZeroCertificate where
  action_zero_to_residual_zero :
    ∀ (A : SU7GaugeFlowActionZeroLaw)
      (n : ℕ) (hn : 2 ≤ n),
      colorLoopTraceResidual n (A.pick n hn).1 (A.pick n hn).2 = 0
  action_zero_to_fixed :
    ∀ (A : SU7GaugeFlowActionZeroLaw)
      (n : ℕ) (hn : 2 ≤ n),
      ResidualTransportFixed
        (colorLoopScalarKeep A.sigma)
        (colorLoopTraceResidual n (A.pick n hn).1 (A.pick n hn).2)
  action_zero_to_fixed_law :
    SU7GaugeFlowActionZeroLaw -> SU7GaugeFlowFixedPointLaw
  action_zero_to_normalizer :
    SU7GaugeFlowActionZeroLaw -> SU7GaugeFlowTraceZeroNormalizer
  action_zero_to_no_gap :
    SU7GaugeFlowActionZeroLaw -> PrimeEdgeTraceSpectrumNoGap
  action_zero_to_no_permanent :
    SU7GaugeFlowActionZeroLaw -> ¬ PermanentPrimeEdgeColorHolonomy
  action_zero_to_primitive :
    SU7GaugeFlowActionZeroLaw -> SU7PrimitiveGaugeDynamicsNormalFormLaw
  action_zero_to_confinement :
    SU7GaugeFlowActionZeroLaw -> SU7ConfinementResidualSplitLaw
  action_zero_to_witness :
    SU7GaugeFlowActionZeroLaw -> ColorLoopUnitBracketFixedPointWitness
  action_zero_to_unit_bracket :
    SU7GaugeFlowActionZeroLaw -> ColorLoopTraceUnitBracketProducer
  action_zero_to_fixed_point :
    SU7GaugeFlowActionZeroLaw -> EvenGoldbachDynamicalFixedPointProducer
  producer_to_fixed_law :
    SU7GaugeFlowActionZeroProducer -> SU7GaugeFlowFixedPointLaw
  producer_to_normalizer :
    SU7GaugeFlowActionZeroProducer -> SU7GaugeFlowTraceZeroNormalizer
  producer_to_no_permanent :
    SU7GaugeFlowActionZeroProducer -> ¬ PermanentPrimeEdgeColorHolonomy
  producer_to_witness :
    SU7GaugeFlowActionZeroProducer -> ColorLoopUnitBracketFixedPointWitness

/-- THEOREM 17: canonical P841 action-zero certificate. -/
def su7GaugeFlowActionZeroCertificate :
    SU7GaugeFlowActionZeroCertificate where
  action_zero_to_residual_zero :=
    gaugeFlowActionZero_traceResidual_zero
  action_zero_to_fixed :=
    gaugeFlowActionZero_fixed
  action_zero_to_fixed_law :=
    gaugeFlowFixedPointLaw_of_actionZeroLaw
  action_zero_to_normalizer :=
    gaugeFlowTraceZeroNormalizer_of_actionZeroLaw
  action_zero_to_no_gap :=
    primeEdgeTraceSpectrumNoGap_of_actionZeroLaw
  action_zero_to_no_permanent :=
    noPermanentColorHolonomy_of_actionZeroLaw
  action_zero_to_primitive :=
    primitiveGaugeDynamics_of_actionZeroLaw
  action_zero_to_confinement :=
    confinementResidualSplitLaw_of_actionZeroLaw
  action_zero_to_witness :=
    colorLoopWitnessOfActionZeroLaw
  action_zero_to_unit_bracket :=
    unitBracketProducer_of_actionZeroLaw
  action_zero_to_fixed_point :=
    fixedPointProducer_of_actionZeroLaw
  producer_to_fixed_law :=
    gaugeFlowFixedPointLaw_of_actionZeroProducer
  producer_to_normalizer :=
    gaugeFlowTraceZeroNormalizer_of_actionZeroProducer
  producer_to_no_permanent :=
    noPermanentColorHolonomy_of_actionZeroProducer
  producer_to_witness :=
    colorLoopWitnessOfActionZeroProducer


end StandardModelConstraint
end SaturationMonoid
