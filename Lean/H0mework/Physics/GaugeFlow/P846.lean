import H0mework.Physics.GaugeFlow.P845

/-!
# Proposition 846: the gauge-flow normalizer is the producer throat

P845 proved that concrete action-zero, active trace-zero, primitive gauge
dynamics, confinement, representation, and spectrum-alpha convergence are
equivalent producer faces.

This file names the narrow throat explicitly:

`SU7GaugeFlowTraceZeroProducer`.

The trace-zero normalizer is equivalent to the global trace-zero sector, and
its existence is equivalent to all producer faces from P845.  Therefore the
remaining lower producer debt is sharply stated: construct the gauge-flow
trace-zero normalizer from the actual SU(7) gauge-flow / representation
dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## The normalizer as the exact trace-zero sector -/

/-- THEOREM 1: a gauge-flow trace-zero normalizer is exactly a global
trace-zero prime-edge sector. -/
def gaugeFlowTraceZeroNormalizer_traceZeroSectorEquiv :
    SU7GaugeFlowTraceZeroNormalizer ≃ TraceZeroPrimeEdgeSector where
  toFun := traceZeroPrimeEdgeSector_of_gaugeFlowNormalizer
  invFun := fun S => { normalForm := S.loop }
  left_inv := by
    intro N
    cases N
    rfl
  right_inv := by
    intro S
    cases S
    rfl

/-- THEOREM 2: trace-zero producer existence is exactly global trace-zero
sector existence. -/
theorem gaugeFlowTraceZeroProducer_iff_traceZeroSector :
    SU7GaugeFlowTraceZeroProducer ↔ Nonempty TraceZeroPrimeEdgeSector := by
  constructor
  · intro H
    rcases H with ⟨N⟩
    exact ⟨traceZeroPrimeEdgeSector_of_gaugeFlowNormalizer N⟩
  · intro H
    rcases H with ⟨S⟩
    exact ⟨{ normalForm := S.loop }⟩

/-! ## Equivalence with primitive dynamics -/

/-- THEOREM 3: primitive gauge dynamics constructs the gauge-flow trace-zero
normalizer. -/
def gaugeFlowTraceZeroNormalizer_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    SU7GaugeFlowTraceZeroNormalizer :=
  gaugeFlowNormalizer_of_activeTraceZeroSector
    (activeTraceZeroSector_of_primitiveGaugeDynamics (1 : ℝ) one_ne_zero G)

/-- THEOREM 4: primitive gauge dynamics constructs the trace-zero producer. -/
theorem gaugeFlowTraceZeroProducer_of_primitiveGaugeDynamics
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    SU7GaugeFlowTraceZeroProducer :=
  ⟨gaugeFlowTraceZeroNormalizer_of_primitiveGaugeDynamics G⟩

/-- THEOREM 5: the gauge-flow trace-zero producer is exactly primitive gauge
dynamics. -/
theorem gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7PrimitiveGaugeDynamicsNormalFormLaw := by
  constructor
  · intro H
    exact primitiveGaugeDynamics_of_gaugeFlowTraceZeroProducer H
  · intro G
    exact gaugeFlowTraceZeroProducer_of_primitiveGaugeDynamics G

/-- THEOREM 6: primitive gauge dynamics is exactly the gauge-flow trace-zero
producer. -/
theorem primitiveGaugeDynamics_iff_gaugeFlowTraceZeroProducer :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7GaugeFlowTraceZeroProducer :=
  gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics.symm

/-! ## The same throat read through every producer face -/

/-- THEOREM 7: the gauge-flow trace-zero producer is exactly the concrete
action-zero producer. -/
theorem gaugeFlowTraceZeroProducer_iff_concreteActionZeroProducer :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7GaugeFlowConcreteActionZeroFiberProducer :=
  gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics.trans
    primitiveGaugeDynamics_iff_concreteActionZeroProducer

/-- THEOREM 8: the concrete action-zero producer is exactly the gauge-flow
trace-zero producer. -/
theorem concreteActionZeroProducer_iff_gaugeFlowTraceZeroProducer :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SU7GaugeFlowTraceZeroProducer :=
  gaugeFlowTraceZeroProducer_iff_concreteActionZeroProducer.symm

/-- THEOREM 9: the gauge-flow trace-zero producer is exactly residual-split
confinement. -/
theorem gaugeFlowTraceZeroProducer_iff_confinementResidualSplitLaw :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7ConfinementResidualSplitLaw :=
  gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics.trans
    primitiveGaugeDynamics_iff_confinementResidualSplitLaw

/-- THEOREM 10: the gauge-flow trace-zero producer is exactly spectrum-resolved
alpha convergence. -/
theorem gaugeFlowTraceZeroProducer_iff_spectrumResolvedAlphaConvergentCarrier :
    SU7GaugeFlowTraceZeroProducer ↔
      SpectrumResolvedAlphaConvergentCarrier :=
  gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics.trans
    primitiveGaugeDynamics_iff_spectrumResolvedAlphaConvergentCarrier

/-- THEOREM 11: the gauge-flow trace-zero producer is exactly the SU(7)
representation allowed-sector law. -/
theorem gaugeFlowTraceZeroProducer_iff_su7RepresentationAllowedSectorLaw :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7RepresentationAllowedSectorLaw :=
  gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics.trans
    primitiveGaugeDynamics_iff_su7RepresentationAllowedSectorLaw

/-! ## Certificate -/

/-- P846 certificate: the trace-zero normalizer is the narrow producer throat;
all action, primitive, confinement, representation, and spectrum-alpha faces
are equivalent to it. -/
structure GaugeFlowTraceZeroProducerThroatCertificate where
  normalizer_equiv_trace_zero_sector :
    SU7GaugeFlowTraceZeroNormalizer ≃ TraceZeroPrimeEdgeSector
  producer_iff_trace_zero_sector :
    SU7GaugeFlowTraceZeroProducer ↔ Nonempty TraceZeroPrimeEdgeSector
  primitive_to_normalizer :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      SU7GaugeFlowTraceZeroNormalizer
  primitive_to_producer :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ->
      SU7GaugeFlowTraceZeroProducer
  producer_iff_primitive :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7PrimitiveGaugeDynamicsNormalFormLaw
  primitive_iff_producer :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7GaugeFlowTraceZeroProducer
  producer_iff_concrete_action :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7GaugeFlowConcreteActionZeroFiberProducer
  producer_iff_confinement :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7ConfinementResidualSplitLaw
  producer_iff_spectrum_alpha :
    SU7GaugeFlowTraceZeroProducer ↔
      SpectrumResolvedAlphaConvergentCarrier
  producer_iff_representation :
    SU7GaugeFlowTraceZeroProducer ↔
      SU7RepresentationAllowedSectorLaw

/-- THEOREM 12: canonical P846 throat certificate. -/
def gaugeFlowTraceZeroProducerThroatCertificate :
    GaugeFlowTraceZeroProducerThroatCertificate where
  normalizer_equiv_trace_zero_sector :=
    gaugeFlowTraceZeroNormalizer_traceZeroSectorEquiv
  producer_iff_trace_zero_sector :=
    gaugeFlowTraceZeroProducer_iff_traceZeroSector
  primitive_to_normalizer :=
    gaugeFlowTraceZeroNormalizer_of_primitiveGaugeDynamics
  primitive_to_producer :=
    gaugeFlowTraceZeroProducer_of_primitiveGaugeDynamics
  producer_iff_primitive :=
    gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics
  primitive_iff_producer :=
    primitiveGaugeDynamics_iff_gaugeFlowTraceZeroProducer
  producer_iff_concrete_action :=
    gaugeFlowTraceZeroProducer_iff_concreteActionZeroProducer
  producer_iff_confinement :=
    gaugeFlowTraceZeroProducer_iff_confinementResidualSplitLaw
  producer_iff_spectrum_alpha :=
    gaugeFlowTraceZeroProducer_iff_spectrumResolvedAlphaConvergentCarrier
  producer_iff_representation :=
    gaugeFlowTraceZeroProducer_iff_su7RepresentationAllowedSectorLaw


end StandardModelConstraint
end SaturationMonoid
