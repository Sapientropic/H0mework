import H0mework.Physics.GaugeFlow.P842

/-!
# Proposition 843: trace-zero sector produces concrete SU(7) action zero

P842 pinned the remaining gauge-flow throat to the concrete action

`S(n,p,q) = colorLoopTraceResidual(n,p,q)^2`.

This file removes one more wrapper: every already-produced trace-zero normal
form is automatically a zero of that concrete action.  Thus the existing
SU(7)-filtered / allowed-sector / representation / confinement / primitive
gauge-dynamics producers now feed directly into the P842 concrete action
zero-fiber law.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Trace-zero sector to concrete action-zero fiber -/

/-- THEOREM 1: a global trace-zero prime-edge sector is a concrete zero fiber
of the SU(7) color-loop action, for any active scalar keep. -/
def concreteActionZeroFiber_of_traceZeroPrimeEdgeSector
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (S : TraceZeroPrimeEdgeSector) :
    SU7GaugeFlowConcreteActionZeroFiberLaw where
  sigma := sigma
  sigma_active := hsigma
  pick := fun n hn =>
    ((S.loop n hn).leftPrime, (S.loop n hn).rightPrime)
  action_zero := by
    intro n hn
    exact
      (su7GaugeFlowColorLoopAction_zero_iff_traceExact n
        (S.loop n hn).leftPrime
        (S.loop n hn).rightPrime).mpr
        (S.loop n hn).trace_zero

/-- THEOREM 2: a trace-zero sector produces the P842 concrete action-zero
producer.  The chosen active scalar is `1`; the action zero itself is
independent of that scalar. -/
def concreteActionZeroFiberProducer_of_traceZeroPrimeEdgeSector
    (S : TraceZeroPrimeEdgeSector) :
    SU7GaugeFlowConcreteActionZeroFiberProducer :=
  ⟨concreteActionZeroFiber_of_traceZeroPrimeEdgeSector
    (1 : ℝ) one_ne_zero S⟩

/-- THEOREM 3: the generated concrete action-zero law preserves the
trace-zero sector's prime-edge endpoints. -/
theorem concreteActionZeroFiber_of_traceZeroPrimeEdgeSector_pick_eq
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (S : TraceZeroPrimeEdgeSector)
    (n : ℕ) (hn : 2 ≤ n) :
    (concreteActionZeroFiber_of_traceZeroPrimeEdgeSector
      sigma hsigma S).pick n hn =
      ((S.loop n hn).leftPrime, (S.loop n hn).rightPrime) :=
  rfl

/-! ## Existing SU(7) producers to concrete action-zero fiber -/

/-- THEOREM 4: an allowed prime-edge sector produces the concrete action-zero
fiber through its canonical trace-zero normal form. -/
def concreteActionZeroFiber_of_allowedPrimeEdgeSector
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (S : SU7AllowedPrimeEdgeSector) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_traceZeroPrimeEdgeSector
    sigma hsigma (su7AllowedPrimeEdgeSectorNormalForm S)

/-- THEOREM 5: a gauge-flow trace-zero normalizer produces the concrete
action-zero fiber directly. -/
def concreteActionZeroFiber_of_gaugeFlowNormalizer
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_traceZeroPrimeEdgeSector
    sigma hsigma (traceZeroPrimeEdgeSector_of_gaugeFlowNormalizer N)

/-- THEOREM 6: a SU(7)-filtered prime-edge loop producer produces the concrete
action-zero fiber through the allowed-sector normal form. -/
def concreteActionZeroFiber_of_su7FilteredProducer
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_allowedPrimeEdgeSector
    sigma hsigma (su7AllowedPrimeEdgeSectorOfFilteredProducer P)

/-- THEOREM 7: a representation allowed-sector law produces the concrete
action-zero fiber. -/
def concreteActionZeroFiber_of_su7RepresentationAllowedSectorLaw
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (L : SU7RepresentationAllowedSectorLaw) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_allowedPrimeEdgeSector
    sigma hsigma (su7AllowedPrimeEdgeSectorOfRepresentationLaw L)

/-- THEOREM 8: residual-split confinement produces the concrete action-zero
fiber. -/
def concreteActionZeroFiber_of_confinementResidualSplitLaw
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (L : SU7ConfinementResidualSplitLaw) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_su7RepresentationAllowedSectorLaw
    sigma hsigma (su7RepresentationAllowedSectorLaw_of_confinementResidualSplitLaw L)

/-- THEOREM 9: spectrum-resolved alpha convergence produces the concrete
action-zero fiber. -/
def concreteActionZeroFiber_of_spectrumResolvedAlphaConvergentCarrier
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_su7RepresentationAllowedSectorLaw
    sigma hsigma
    (su7RepresentationAllowedSectorLaw_of_spectrumResolvedAlphaConvergentCarrier C)

/-- THEOREM 10: primitive SU(7) gauge dynamics produces the concrete
action-zero fiber. -/
def concreteActionZeroFiber_of_primitiveGaugeDynamics
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_su7RepresentationAllowedSectorLaw
    sigma hsigma (su7RepresentationAllowedSectorLaw_of_primitiveGaugeDynamics G)

/-- THEOREM 11: the alpha-convergent carrier nail produces the concrete
action-zero fiber through the representation allowed-sector law. -/
def concreteActionZeroFiber_of_alphaStrongConvergentCarrierNail
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (H : AlphaStrongConvergentCarrierNail) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_su7RepresentationAllowedSectorLaw
    sigma hsigma (su7RepresentationAllowedSectorLaw_of_alphaStrongConvergentCarrierNail H)

/-! ## Producer-level readouts -/

/-- THEOREM 12: a SU(7)-filtered producer gives a P842 concrete action-zero
producer. -/
def concreteActionZeroProducer_of_su7FilteredProducer
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    SU7GaugeFlowConcreteActionZeroFiberProducer :=
  ⟨concreteActionZeroFiber_of_su7FilteredProducer
    (1 : ℝ) one_ne_zero P⟩

/-- THEOREM 13: a representation law gives a P842 concrete action-zero
producer. -/
def concreteActionZeroProducer_of_su7RepresentationAllowedSectorLaw
    (L : SU7RepresentationAllowedSectorLaw) :
    SU7GaugeFlowConcreteActionZeroFiberProducer :=
  ⟨concreteActionZeroFiber_of_su7RepresentationAllowedSectorLaw
    (1 : ℝ) one_ne_zero L⟩

/-- THEOREM 14: residual-split confinement gives a P842 concrete action-zero
producer. -/
def concreteActionZeroProducer_of_confinementResidualSplitLaw
    (L : SU7ConfinementResidualSplitLaw) :
    SU7GaugeFlowConcreteActionZeroFiberProducer :=
  ⟨concreteActionZeroFiber_of_confinementResidualSplitLaw
    (1 : ℝ) one_ne_zero L⟩

/-- THEOREM 15: primitive gauge dynamics gives a P842 concrete action-zero
producer. -/
def concreteActionZeroProducer_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    SU7GaugeFlowConcreteActionZeroFiberProducer :=
  ⟨concreteActionZeroFiber_of_primitiveGaugeDynamics
    (1 : ℝ) one_ne_zero G⟩

/-- THEOREM 16: a spectrum-resolved alpha convergent carrier gives a P842
concrete action-zero producer. -/
def concreteActionZeroProducer_of_spectrumResolvedAlphaConvergentCarrier
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    SU7GaugeFlowConcreteActionZeroFiberProducer :=
  ⟨concreteActionZeroFiber_of_spectrumResolvedAlphaConvergentCarrier
    (1 : ℝ) one_ne_zero C⟩

/-- THEOREM 17: a concrete action-zero producer produced from primitive gauge
dynamics forbids permanent color holonomy by the P842/P841/P840 chain. -/
theorem noPermanentColorHolonomy_of_primitiveGaugeDynamics_via_concreteAction
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    ¬ PermanentPrimeEdgeColorHolonomy :=
  noPermanentColorHolonomy_of_concreteActionZeroFiberProducer
    (concreteActionZeroProducer_of_primitiveGaugeDynamics G)

/-- THEOREM 18: a concrete action-zero producer produced from spectrum-resolved
alpha convergence yields the spectrum-resolved alpha convergent carrier readout
again through the P842/P841/P840 chain. -/
theorem spectrumResolvedAlphaConvergentCarrier_via_concreteAction
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    SpectrumResolvedAlphaConvergentCarrier :=
  spectrumResolvedAlphaConvergentCarrier_of_concreteActionZeroFiber
    (concreteActionZeroFiber_of_spectrumResolvedAlphaConvergentCarrier
      (1 : ℝ) one_ne_zero C)

/-! ## Certificate -/

/-- P843 certificate: every trace-zero/allowed/representation/confinement
producer already produces the concrete action zero-fiber of P842. -/
structure TraceZeroToConcreteActionZeroCertificate where
  trace_zero_sector_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      TraceZeroPrimeEdgeSector -> SU7GaugeFlowConcreteActionZeroFiberLaw
  trace_zero_sector_to_producer :
    TraceZeroPrimeEdgeSector -> SU7GaugeFlowConcreteActionZeroFiberProducer
  allowed_sector_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7AllowedPrimeEdgeSector -> SU7GaugeFlowConcreteActionZeroFiberLaw
  normalizer_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7GaugeFlowTraceZeroNormalizer -> SU7GaugeFlowConcreteActionZeroFiberLaw
  filtered_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7FilteredPrimeEdgeLoopProducer -> SU7GaugeFlowConcreteActionZeroFiberLaw
  representation_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7RepresentationAllowedSectorLaw -> SU7GaugeFlowConcreteActionZeroFiberLaw
  confinement_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7ConfinementResidualSplitLaw -> SU7GaugeFlowConcreteActionZeroFiberLaw
  spectrum_alpha_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SpectrumResolvedAlphaConvergentCarrier -> SU7GaugeFlowConcreteActionZeroFiberLaw
  primitive_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7PrimitiveGaugeDynamicsNormalFormLaw -> SU7GaugeFlowConcreteActionZeroFiberLaw
  alpha_nail_to_concrete :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      AlphaStrongConvergentCarrierNail -> SU7GaugeFlowConcreteActionZeroFiberLaw
  primitive_to_no_permanent_via_concrete :
    SU7PrimitiveGaugeDynamicsNormalFormLaw -> ¬ PermanentPrimeEdgeColorHolonomy

/-- THEOREM 19: canonical P843 trace-zero to concrete action-zero certificate.
-/
def traceZeroToConcreteActionZeroCertificate :
    TraceZeroToConcreteActionZeroCertificate where
  trace_zero_sector_to_concrete :=
    concreteActionZeroFiber_of_traceZeroPrimeEdgeSector
  trace_zero_sector_to_producer :=
    concreteActionZeroFiberProducer_of_traceZeroPrimeEdgeSector
  allowed_sector_to_concrete :=
    concreteActionZeroFiber_of_allowedPrimeEdgeSector
  normalizer_to_concrete :=
    concreteActionZeroFiber_of_gaugeFlowNormalizer
  filtered_to_concrete :=
    concreteActionZeroFiber_of_su7FilteredProducer
  representation_to_concrete :=
    concreteActionZeroFiber_of_su7RepresentationAllowedSectorLaw
  confinement_to_concrete :=
    concreteActionZeroFiber_of_confinementResidualSplitLaw
  spectrum_alpha_to_concrete :=
    concreteActionZeroFiber_of_spectrumResolvedAlphaConvergentCarrier
  primitive_to_concrete :=
    concreteActionZeroFiber_of_primitiveGaugeDynamics
  alpha_nail_to_concrete :=
    concreteActionZeroFiber_of_alphaStrongConvergentCarrierNail
  primitive_to_no_permanent_via_concrete :=
    noPermanentColorHolonomy_of_primitiveGaugeDynamics_via_concreteAction


end StandardModelConstraint
end SaturationMonoid
