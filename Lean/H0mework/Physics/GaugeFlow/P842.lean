import H0mework.Physics.GaugeFlow.P841

/-!
# Proposition 842: concrete SU(7) color-loop action functional

P841 made the remaining gauge-flow throat an action-zero law.  This file pins
the action itself to the concrete color-loop functional already introduced in
P811:

`S(n,p,q) = colorLoopTraceEnergy n p q = colorLoopTraceResidual(n,p,q)^2`.

Thus the zero-fiber is no longer an unnamed receipt.  It is the zero-fiber of a
specific positive scalar action functional, and Lean proves that this zero
fiber is exactly the trace-exact / fixed-residual / no-gap producer chain.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Concrete action functional -/

/-- The concrete SU(7) color-loop action on the prime-edge fiber `2n`.

It is exactly the squared trace residual of the color-loop matrix
`diag(p,q,-2n)`. -/
def su7GaugeFlowColorLoopAction
    (n : ℕ) (p q : PrimeExponent) : ℝ :=
  colorLoopTraceEnergy n p q

/-- THEOREM 1: the concrete action is the positive scalar residual energy used
by the truth-formula core. -/
theorem su7GaugeFlowColorLoopAction_eq_scalarResidualEnergy
    (n : ℕ) (p q : PrimeExponent) :
    su7GaugeFlowColorLoopAction n p q =
      colorLoopScalarResidualEnergy (colorLoopTraceResidual n p q) := by
  rfl

/-- THEOREM 2: the concrete action is the square of the trace residual. -/
theorem su7GaugeFlowColorLoopAction_eq_residual_sq
    (n : ℕ) (p q : PrimeExponent) :
    su7GaugeFlowColorLoopAction n p q =
      (colorLoopTraceResidual n p q) ^ 2 := by
  rfl

/-- THEOREM 3: the concrete action's zero fiber is exactly trace exactness. -/
theorem su7GaugeFlowColorLoopAction_zero_iff_traceExact
    (n : ℕ) (p q : PrimeExponent) :
    su7GaugeFlowColorLoopAction n p q = 0 ↔
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) := by
  rw [su7GaugeFlowColorLoopAction_eq_scalarResidualEnergy,
    colorLoopScalarResidualEnergy_zero_iff]
  exact (colorLoopTraceExact_iff_traceResidual_zero n p q).symm

/-- THEOREM 4: on an active scalar keep, the concrete action's zero fiber is
exactly fixed residual transport. -/
theorem su7GaugeFlowColorLoopAction_zero_iff_fixed
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (n : ℕ) (p q : PrimeExponent) :
    su7GaugeFlowColorLoopAction n p q = 0 ↔
      ResidualTransportFixed
        (colorLoopScalarKeep sigma) (colorLoopTraceResidual n p q) := by
  rw [su7GaugeFlowColorLoopAction_eq_scalarResidualEnergy]
  exact
    (colorLoopResidualSplitCoreEquivalence sigma hsigma n p q).fixed_iff_zero_energy.symm

/-- THEOREM 5: the concrete action's zero fiber is the prime-pair equation. -/
theorem su7GaugeFlowColorLoopAction_zero_iff_primePair
    (n : ℕ) (p q : PrimeExponent) :
    su7GaugeFlowColorLoopAction n p q = 0 ↔
      2 * n = p.1 + q.1 := by
  exact colorLoopTraceEnergy_zero_iff_goldbach_pair n p q

/-! ## Zero-fiber law for the concrete action -/

/-- Concrete action-zero law.

Unlike P841's law, this names the action functional being zero:
`su7GaugeFlowColorLoopAction`. -/
structure SU7GaugeFlowConcreteActionZeroFiberLaw where
  sigma : ℝ
  sigma_active : sigma ≠ 0
  pick : (n : ℕ) -> 2 ≤ n -> PrimeExponent × PrimeExponent
  action_zero :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      su7GaugeFlowColorLoopAction n (pick n hn).1 (pick n hn).2 = 0

/-- The proposition that the concrete action has a global zero fiber. -/
def SU7GaugeFlowConcreteActionZeroFiberProducer : Prop :=
  Nonempty SU7GaugeFlowConcreteActionZeroFiberLaw

/-- THEOREM 6: a concrete action-zero law generates P841's action-zero law. -/
def gaugeFlowActionZeroLaw_of_concreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    SU7GaugeFlowActionZeroLaw where
  sigma := C.sigma
  sigma_active := C.sigma_active
  pick := C.pick
  action_zero := by
    intro n hn
    rw [← su7GaugeFlowColorLoopAction_eq_scalarResidualEnergy]
    exact C.action_zero n hn

/-- THEOREM 7: a concrete action-zero law generates the fixed-point law. -/
def gaugeFlowFixedPointLaw_of_concreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    SU7GaugeFlowFixedPointLaw :=
  gaugeFlowFixedPointLaw_of_actionZeroLaw
    (gaugeFlowActionZeroLaw_of_concreteActionZeroFiber C)

/-- THEOREM 8: a concrete action-zero law generates the trace-zero
normalizer. -/
def gaugeFlowTraceZeroNormalizer_of_concreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    SU7GaugeFlowTraceZeroNormalizer :=
  gaugeFlowTraceZeroNormalizer_of_actionZeroLaw
    (gaugeFlowActionZeroLaw_of_concreteActionZeroFiber C)

/-- THEOREM 9: a concrete action-zero law proves no trace-spectrum gap. -/
theorem primeEdgeTraceSpectrumNoGap_of_concreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    PrimeEdgeTraceSpectrumNoGap :=
  primeEdgeTraceSpectrumNoGap_of_actionZeroLaw
    (gaugeFlowActionZeroLaw_of_concreteActionZeroFiber C)

/-- THEOREM 10: a concrete action-zero law forbids permanent color holonomy. -/
theorem noPermanentColorHolonomy_of_concreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  noPermanentColorHolonomy_of_actionZeroLaw
    (gaugeFlowActionZeroLaw_of_concreteActionZeroFiber C)

/-- THEOREM 11: a concrete action-zero law produces the color-loop witness. -/
def colorLoopWitnessOfConcreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitnessOfActionZeroLaw
    (gaugeFlowActionZeroLaw_of_concreteActionZeroFiber C)

/-- THEOREM 12: a concrete action-zero law produces the spectrum-resolved
alpha convergent carrier. -/
theorem spectrumResolvedAlphaConvergentCarrier_of_concreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    SpectrumResolvedAlphaConvergentCarrier :=
  spectrumResolvedAlphaConvergentCarrier_of_actionZeroLaw
    (gaugeFlowActionZeroLaw_of_concreteActionZeroFiber C)

/-! ## Producer-level readouts -/

/-- THEOREM 13: existence of a concrete action zero fiber produces P841's
action-zero law. -/
def gaugeFlowActionZeroLaw_of_concreteActionZeroFiberProducer
    (H : SU7GaugeFlowConcreteActionZeroFiberProducer) :
    SU7GaugeFlowActionZeroLaw :=
  gaugeFlowActionZeroLaw_of_concreteActionZeroFiber (Classical.choice H)

/-- THEOREM 14: existence of a concrete action zero fiber produces P840's
fixed-point law. -/
def gaugeFlowFixedPointLaw_of_concreteActionZeroFiberProducer
    (H : SU7GaugeFlowConcreteActionZeroFiberProducer) :
    SU7GaugeFlowFixedPointLaw :=
  gaugeFlowFixedPointLaw_of_concreteActionZeroFiber (Classical.choice H)

/-- THEOREM 15: existence of a concrete action zero fiber forbids permanent
color holonomy. -/
theorem noPermanentColorHolonomy_of_concreteActionZeroFiberProducer
    (H : SU7GaugeFlowConcreteActionZeroFiberProducer) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  noPermanentColorHolonomy_of_concreteActionZeroFiber (Classical.choice H)

/-! ## Certificate -/

/-- P842 certificate: the concrete action functional and its zero-fiber
producer generate the whole P841/P840/P839 chain. -/
structure SU7GaugeFlowConcreteActionFunctionalCertificate where
  action_eq_scalar_energy :
    ∀ (n : ℕ) (p q : PrimeExponent),
      su7GaugeFlowColorLoopAction n p q =
        colorLoopScalarResidualEnergy (colorLoopTraceResidual n p q)
  action_eq_residual_sq :
    ∀ (n : ℕ) (p q : PrimeExponent),
      su7GaugeFlowColorLoopAction n p q =
        (colorLoopTraceResidual n p q) ^ 2
  action_zero_iff_trace_exact :
    ∀ (n : ℕ) (p q : PrimeExponent),
      su7GaugeFlowColorLoopAction n p q = 0 ↔
        ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q)
  action_zero_iff_fixed :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      ∀ (n : ℕ) (p q : PrimeExponent),
        su7GaugeFlowColorLoopAction n p q = 0 ↔
          ResidualTransportFixed
            (colorLoopScalarKeep sigma) (colorLoopTraceResidual n p q)
  action_zero_iff_prime_pair :
    ∀ (n : ℕ) (p q : PrimeExponent),
      su7GaugeFlowColorLoopAction n p q = 0 ↔
        2 * n = p.1 + q.1
  concrete_to_action_zero :
    SU7GaugeFlowConcreteActionZeroFiberLaw -> SU7GaugeFlowActionZeroLaw
  concrete_to_fixed_law :
    SU7GaugeFlowConcreteActionZeroFiberLaw -> SU7GaugeFlowFixedPointLaw
  concrete_to_normalizer :
    SU7GaugeFlowConcreteActionZeroFiberLaw -> SU7GaugeFlowTraceZeroNormalizer
  concrete_to_no_gap :
    SU7GaugeFlowConcreteActionZeroFiberLaw -> PrimeEdgeTraceSpectrumNoGap
  concrete_to_no_permanent :
    SU7GaugeFlowConcreteActionZeroFiberLaw -> ¬ PermanentPrimeEdgeColorHolonomy
  concrete_to_witness :
    SU7GaugeFlowConcreteActionZeroFiberLaw -> ColorLoopUnitBracketFixedPointWitness
  concrete_to_alpha_convergence :
    SU7GaugeFlowConcreteActionZeroFiberLaw -> SpectrumResolvedAlphaConvergentCarrier
  producer_to_action_zero :
    SU7GaugeFlowConcreteActionZeroFiberProducer -> SU7GaugeFlowActionZeroLaw
  producer_to_fixed_law :
    SU7GaugeFlowConcreteActionZeroFiberProducer -> SU7GaugeFlowFixedPointLaw
  producer_to_no_permanent :
    SU7GaugeFlowConcreteActionZeroFiberProducer -> ¬ PermanentPrimeEdgeColorHolonomy

/-- THEOREM 16: canonical P842 concrete action-functional certificate. -/
def su7GaugeFlowConcreteActionFunctionalCertificate :
    SU7GaugeFlowConcreteActionFunctionalCertificate where
  action_eq_scalar_energy :=
    su7GaugeFlowColorLoopAction_eq_scalarResidualEnergy
  action_eq_residual_sq :=
    su7GaugeFlowColorLoopAction_eq_residual_sq
  action_zero_iff_trace_exact :=
    su7GaugeFlowColorLoopAction_zero_iff_traceExact
  action_zero_iff_fixed := by
    intro sigma hsigma n p q
    exact su7GaugeFlowColorLoopAction_zero_iff_fixed sigma hsigma n p q
  action_zero_iff_prime_pair :=
    su7GaugeFlowColorLoopAction_zero_iff_primePair
  concrete_to_action_zero :=
    gaugeFlowActionZeroLaw_of_concreteActionZeroFiber
  concrete_to_fixed_law :=
    gaugeFlowFixedPointLaw_of_concreteActionZeroFiber
  concrete_to_normalizer :=
    gaugeFlowTraceZeroNormalizer_of_concreteActionZeroFiber
  concrete_to_no_gap :=
    primeEdgeTraceSpectrumNoGap_of_concreteActionZeroFiber
  concrete_to_no_permanent :=
    noPermanentColorHolonomy_of_concreteActionZeroFiber
  concrete_to_witness :=
    colorLoopWitnessOfConcreteActionZeroFiber
  concrete_to_alpha_convergence :=
    spectrumResolvedAlphaConvergentCarrier_of_concreteActionZeroFiber
  producer_to_action_zero :=
    gaugeFlowActionZeroLaw_of_concreteActionZeroFiberProducer
  producer_to_fixed_law :=
    gaugeFlowFixedPointLaw_of_concreteActionZeroFiberProducer
  producer_to_no_permanent :=
    noPermanentColorHolonomy_of_concreteActionZeroFiberProducer


end StandardModelConstraint
end SaturationMonoid
