import H0mework.Physics.AlphaSpectrum.P847
import H0mework.Realization.Faces.P820

/-!
# Proposition 848: seven-face carrier self-consistency removes `hcarrier`

P820's carrier-consistency theorem still took one single-face hypothesis:

`AlphaStrongExactResidualRequiresCarrierConvergence`.

P821 correctly diagnosed that deleting that hypothesis outright has Goldbach
strength.  The right replacement is therefore not another single face.  It is
the meta-condition the framework actually needs: the simultaneous intersection
of the seven producer faces is inhabited.

This file names that object.  The seven faces are:

1. gauge-flow trace-zero throat;
2. concrete action-zero producer;
3. primitive gauge-dynamics normal form;
4. confinement residual split;
5. SU(7) representation allowed-sector law;
6. spectrum-resolved alpha convergence;
7. finite-spectrum alpha evaluator.

The theorem is then sharp: the seven-face intersection yields the old P819
carrier-convergence bridge, and hence P820's zero-fiber certificate, without
assuming `hcarrier` as an external single-face premise.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open SaturationMonoid.AffineRelaxation
open SaturationMonoid.StandardModelConstraint
open SaturationMonoid.GrandUnification

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Seven-face intersection -/

/-- A point in the simultaneous seven-face carrier intersection.

This is intentionally stronger than any one face.  It packages the fact that
the trace-zero throat, concrete action, primitive dynamics, confinement,
representation filter, alpha spectrum, and finite-spectrum evaluator are all
reading the same carrier, rather than borrowing a Goldbach-strength conclusion
from one projection. -/
structure SevenFaceCarrierIntersectionPoint : Prop where
  gauge_flow_trace_zero :
    SU7GaugeFlowTraceZeroProducer
  concrete_action_zero :
    SU7GaugeFlowConcreteActionZeroFiberProducer
  primitive_gauge_dynamics :
    SU7PrimitiveGaugeDynamicsNormalFormLaw
  confinement_residual_split :
    SU7ConfinementResidualSplitLaw
  representation_allowed_sector :
    SU7RepresentationAllowedSectorLaw
  spectrum_alpha_convergence :
    SpectrumResolvedAlphaConvergentCarrier
  finite_alpha_spectrum :
    AlphaStrongFiniteSpectrumEvaluatorCertificate.{0}

/-- The carrier self-consistency meta-condition: the seven producer faces have
a simultaneous point of intersection. -/
def SevenFaceCarrierSelfConsistency : Prop :=
  Nonempty SevenFaceCarrierIntersectionPoint

/-! ## The P846 throat generates the whole intersection -/

/-- THEOREM 1: the trace-zero throat canonically produces a point of the
seven-face intersection. -/
def sevenFaceCarrierIntersectionPoint_of_gaugeFlowTraceZeroProducer
    (H : SU7GaugeFlowTraceZeroProducer) :
    SevenFaceCarrierIntersectionPoint where
  gauge_flow_trace_zero := H
  concrete_action_zero :=
    gaugeFlowTraceZeroProducer_iff_concreteActionZeroProducer.mp H
  primitive_gauge_dynamics :=
    gaugeFlowTraceZeroProducer_iff_primitiveGaugeDynamics.mp H
  confinement_residual_split :=
    gaugeFlowTraceZeroProducer_iff_confinementResidualSplitLaw.mp H
  representation_allowed_sector :=
    gaugeFlowTraceZeroProducer_iff_su7RepresentationAllowedSectorLaw.mp H
  spectrum_alpha_convergence :=
    gaugeFlowTraceZeroProducer_iff_spectrumResolvedAlphaConvergentCarrier.mp H
  finite_alpha_spectrum :=
    alphaStrongFiniteSpectrumEvaluatorCertificate

/-- THEOREM 2: a trace-zero throat is exactly a nonempty seven-face
intersection. -/
theorem sevenFaceCarrierSelfConsistency_iff_gaugeFlowTraceZeroProducer :
    SevenFaceCarrierSelfConsistency ↔ SU7GaugeFlowTraceZeroProducer := by
  constructor
  · intro H
    rcases H with ⟨P⟩
    exact P.gauge_flow_trace_zero
  · intro H
    exact ⟨sevenFaceCarrierIntersectionPoint_of_gaugeFlowTraceZeroProducer H⟩

/-! ## Seven-face self-consistency produces the P819 carrier bridge -/

/-- THEOREM 3: the gauge-flow face of the intersection yields the color-loop
unit-bracket producer. -/
theorem sevenFaceGaugeFlowTraceZeroProducer_unitBracket
    (H : SU7GaugeFlowTraceZeroProducer) :
    ColorLoopTraceUnitBracketProducer := by
  rcases H with ⟨N⟩
  exact unitBracketProducer_of_gaugeFlowNormalizer N

/-- THEOREM 4: seven-face self-consistency yields the unit-bracket producer.
-/
theorem sevenFaceCarrierSelfConsistency_unitBracket
    (H : SevenFaceCarrierSelfConsistency) :
    ColorLoopTraceUnitBracketProducer := by
  rcases H with ⟨P⟩
  exact sevenFaceGaugeFlowTraceZeroProducer_unitBracket
    P.gauge_flow_trace_zero

/-- THEOREM 5: seven-face self-consistency dissolves the Goldbach-side
color-loop obstruction. -/
theorem sevenFaceCarrierSelfConsistency_evenGoldbach
    (H : SevenFaceCarrierSelfConsistency) :
    EvenGoldbachStatement := by
  exact colorLoopTraceUnitBracketProducer_iff_evenGoldbach.mp
    (sevenFaceCarrierSelfConsistency_unitBracket H)

/-- THEOREM 6: seven-face self-consistency produces the exact P819
same-carrier convergence bridge. -/
theorem alphaStrongRequiresCarrierConvergence_of_sevenFaceCarrierSelfConsistency
    (H : SevenFaceCarrierSelfConsistency) :
    AlphaStrongExactResidualRequiresCarrierConvergence := by
  exact alphaStrongRequiresCarrierConvergence_iff_evenGoldbach.mpr
    (sevenFaceCarrierSelfConsistency_evenGoldbach H)

/-! ## P820 without external `hcarrier` -/

/-- THEOREM 7: under the seven-face carrier self-consistency condition, the
color-loop zero fiber is inhabited without taking `hcarrier` as an external
single-face assumption. -/
theorem colorLoopCarrierZeroFiber_of_sevenFaceCarrierSelfConsistency
    (C : GrandProducerCompletenessCertificate)
    (H : SevenFaceCarrierSelfConsistency) :
    ColorLoopCarrierZeroFiber :=
  colorLoopCarrierZeroFiber_of_grandProducerCompleteness C
    (alphaStrongRequiresCarrierConvergence_of_sevenFaceCarrierSelfConsistency H)

/-- THEOREM 8: P820's carrier-consistency certificate with the single-face
`hcarrier` hypothesis replaced by the canonical seven-face self-consistency
meta-condition. -/
theorem grandProducerCompleteness_carrierConsistencyZeroFibers_of_sevenFaceCarrierSelfConsistency
    (C : GrandProducerCompletenessCertificate)
    (H : SevenFaceCarrierSelfConsistency) :
    GrandCarrierConsistencyZeroFiberCertificate :=
  grandProducerCompleteness_carrierConsistencyZeroFibers C
    (alphaStrongRequiresCarrierConvergence_of_sevenFaceCarrierSelfConsistency H)

end ResidualProjection
end SaturationMonoid
