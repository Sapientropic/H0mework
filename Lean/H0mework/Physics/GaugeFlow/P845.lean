import H0mework.Physics.GaugeFlow.P844

/-!
# Proposition 845: primitive gauge dynamics is active trace-zero action

P844 proved:

`SU7GaugeFlowConcreteActionZeroFiberLaw ≃ ActiveTraceZeroPrimeEdgeSector`.

This file closes the remaining direction against the primitive gauge dynamics
object.  An active trace-zero sector directly supplies a gauge-flow
trace-zero normalizer, hence primitive SU(7) gauge dynamics.  Therefore

`concrete action-zero producer`,
`active trace-zero sector`, and
`primitive gauge dynamics`

are equivalent producer faces.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Active trace-zero sector to primitive gauge dynamics -/

/-- THEOREM 1: an active trace-zero sector is already a gauge-flow
trace-zero normalizer; the scalar coordinate is irrelevant to the normal form
itself. -/
def gaugeFlowNormalizer_of_activeTraceZeroSector
    (A : ActiveTraceZeroPrimeEdgeSector) :
    SU7GaugeFlowTraceZeroNormalizer where
  normalForm := A.sector.loop

/-- THEOREM 2: an active trace-zero sector produces primitive SU(7) gauge
dynamics. -/
theorem primitiveGaugeDynamics_of_activeTraceZeroSector
    (A : ActiveTraceZeroPrimeEdgeSector) :
    SU7PrimitiveGaugeDynamicsNormalFormLaw :=
  primitiveGaugeDynamics_of_gaugeFlowNormalizer
    (gaugeFlowNormalizer_of_activeTraceZeroSector A)

/-- THEOREM 3: active trace-zero sector existence is exactly primitive gauge
dynamics. -/
theorem activeTraceZeroSector_iff_primitiveGaugeDynamics :
    Nonempty ActiveTraceZeroPrimeEdgeSector ↔
      SU7PrimitiveGaugeDynamicsNormalFormLaw := by
  constructor
  · intro H
    exact primitiveGaugeDynamics_of_activeTraceZeroSector (Classical.choice H)
  · intro G
    exact ⟨activeTraceZeroSector_of_primitiveGaugeDynamics
      (1 : ℝ) one_ne_zero G⟩

/-- THEOREM 4: primitive gauge dynamics is exactly active trace-zero sector
existence. -/
theorem primitiveGaugeDynamics_iff_activeTraceZeroSector :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      Nonempty ActiveTraceZeroPrimeEdgeSector :=
  activeTraceZeroSector_iff_primitiveGaugeDynamics.symm

/-- THEOREM 5: a concrete action-zero producer is exactly primitive SU(7)
gauge dynamics. -/
theorem concreteActionZeroProducer_iff_primitiveGaugeDynamics :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SU7PrimitiveGaugeDynamicsNormalFormLaw := by
  exact
    concreteActionZeroProducer_iff_activeTraceZeroSector.trans
      activeTraceZeroSector_iff_primitiveGaugeDynamics

/-- THEOREM 6: primitive SU(7) gauge dynamics is exactly the concrete
action-zero producer. -/
theorem primitiveGaugeDynamics_iff_concreteActionZeroProducer :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7GaugeFlowConcreteActionZeroFiberProducer :=
  concreteActionZeroProducer_iff_primitiveGaugeDynamics.symm

/-! ## Transport to the other producer faces -/

/-- THEOREM 7: a concrete action-zero producer is exactly residual-split
confinement. -/
theorem concreteActionZeroProducer_iff_confinementResidualSplitLaw :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SU7ConfinementResidualSplitLaw :=
  concreteActionZeroProducer_iff_primitiveGaugeDynamics.trans
    primitiveGaugeDynamics_iff_confinementResidualSplitLaw

/-- THEOREM 8: a concrete action-zero producer is exactly spectrum-resolved
alpha convergence. -/
theorem concreteActionZeroProducer_iff_spectrumResolvedAlphaConvergentCarrier :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SpectrumResolvedAlphaConvergentCarrier :=
  concreteActionZeroProducer_iff_primitiveGaugeDynamics.trans
    primitiveGaugeDynamics_iff_spectrumResolvedAlphaConvergentCarrier

/-- THEOREM 9: a concrete action-zero producer is exactly the SU(7)
representation allowed-sector law. -/
theorem concreteActionZeroProducer_iff_su7RepresentationAllowedSectorLaw :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SU7RepresentationAllowedSectorLaw :=
  concreteActionZeroProducer_iff_primitiveGaugeDynamics.trans
    primitiveGaugeDynamics_iff_su7RepresentationAllowedSectorLaw

/-- THEOREM 10: spectrum-resolved alpha convergence is exactly the concrete
action-zero producer. -/
theorem spectrumResolvedAlphaConvergentCarrier_iff_concreteActionZeroProducer :
    SpectrumResolvedAlphaConvergentCarrier ↔
      SU7GaugeFlowConcreteActionZeroFiberProducer :=
  concreteActionZeroProducer_iff_spectrumResolvedAlphaConvergentCarrier.symm

/-! ## Certificate -/

/-- P845 certificate: the concrete action face, active trace-zero sector,
primitive gauge dynamics, confinement, representation, and spectrum-alpha
faces are equivalent. -/
structure PrimitiveGaugeDynamicsConcreteActionEquivalenceCertificate where
  active_to_normalizer :
    ActiveTraceZeroPrimeEdgeSector -> SU7GaugeFlowTraceZeroNormalizer
  active_to_primitive :
    ActiveTraceZeroPrimeEdgeSector -> SU7PrimitiveGaugeDynamicsNormalFormLaw
  active_iff_primitive :
    Nonempty ActiveTraceZeroPrimeEdgeSector ↔
      SU7PrimitiveGaugeDynamicsNormalFormLaw
  primitive_iff_active :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      Nonempty ActiveTraceZeroPrimeEdgeSector
  concrete_iff_primitive :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SU7PrimitiveGaugeDynamicsNormalFormLaw
  primitive_iff_concrete :
    SU7PrimitiveGaugeDynamicsNormalFormLaw ↔
      SU7GaugeFlowConcreteActionZeroFiberProducer
  concrete_iff_confinement :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SU7ConfinementResidualSplitLaw
  concrete_iff_spectrum_alpha :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SpectrumResolvedAlphaConvergentCarrier
  concrete_iff_representation :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      SU7RepresentationAllowedSectorLaw

/-- THEOREM 11: canonical P845 equivalence certificate. -/
def primitiveGaugeDynamicsConcreteActionEquivalenceCertificate :
    PrimitiveGaugeDynamicsConcreteActionEquivalenceCertificate where
  active_to_normalizer :=
    gaugeFlowNormalizer_of_activeTraceZeroSector
  active_to_primitive :=
    primitiveGaugeDynamics_of_activeTraceZeroSector
  active_iff_primitive :=
    activeTraceZeroSector_iff_primitiveGaugeDynamics
  primitive_iff_active :=
    primitiveGaugeDynamics_iff_activeTraceZeroSector
  concrete_iff_primitive :=
    concreteActionZeroProducer_iff_primitiveGaugeDynamics
  primitive_iff_concrete :=
    primitiveGaugeDynamics_iff_concreteActionZeroProducer
  concrete_iff_confinement :=
    concreteActionZeroProducer_iff_confinementResidualSplitLaw
  concrete_iff_spectrum_alpha :=
    concreteActionZeroProducer_iff_spectrumResolvedAlphaConvergentCarrier
  concrete_iff_representation :=
    concreteActionZeroProducer_iff_su7RepresentationAllowedSectorLaw


end StandardModelConstraint
end SaturationMonoid
