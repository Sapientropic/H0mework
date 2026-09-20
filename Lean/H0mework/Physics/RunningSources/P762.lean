import H0mework.Realization.RelaxationFlow.P476
import H0mework.Physics.JointSources.P523

namespace SaturationMonoid
namespace StandardModelConstraint

/-!
# Proposition 762: SU(7) representation-physicalized RG-flow producer

This file keeps the representation-physicalization step out of the large grand
inventory file.  It welds the already-proved finite SU(7) representation
receipt to the one-loop inverse-coordinate flow:

* the concrete `diag(C,W,z,z⁻¹)` block embedding is injective;
* the incidence carrier supplies the matter/Higgs trace input;
* the finite multiplet carrier is anomaly-free;
* oriented anomaly equations select the Standard-Model hypercharge branch;
* the QCD incidence input gives `b0 = 7`;
* the same `b0` is the color inverse-coupling RG-flow slope.
-/

open RunningSigmaBeta

/-- A compact certificate for the representation-physicalized QCD/RG producer
layer. -/
structure SU7RepresentationPhysicalizedRGFlowProducerCertificate : Prop where
  representation_physicalization :
    Nonempty SU7RepresentationPhysicalizationReceipt
  block_embedding_injective :
    Function.Injective GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7
  incidence_matter_carrier :
    Nonempty SU7BlockIncidenceMatterCarrierCertificate
  incidence_reconstructs_qcd_trace :
    qcdBlockIncidenceOneLoopInput = incidenceCarrierTraceInput .colorSU3
  anomaly_cancellation :
    Nonempty StandardModelMultipletAnomalyCancellationCertificate
  oriented_hypercharge_unique :
    ∀ Y : OneGenerationHyperchargeAssignment,
      Y.colorAnomalyFree ->
      Y.weakAnomalyFree ->
      Y.gravitationalAnomalyFree ->
      Y.cubicAnomalyFree ->
      Y.e = 1 ->
      Y.u < Y.d ->
      Y = OneGenerationHyperchargeAssignment.standardModel
  representation_qcd_b0 :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7
  qcd_b0_and_alpha_gap :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
      0 < alphaStrongTwoLoopSMDisplayedGap ℚ
  qcd_inverse_flow_slope_from_representation :
    ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / standardModelOneLoopSigmaFlow .colorSU3 sigma0 t =
        (1 : ℝ) / sigma0 +
          ((betaCoeff qcdBlockIncidenceOneLoopInput : ℚ) : ℝ) * t

/-- THEOREM: the current finite SU(7) representation-physicalization layer
feeds the certified QCD one-loop RG-flow slope. -/
theorem su7RepresentationPhysicalizedRGFlowProducerCertificate :
    SU7RepresentationPhysicalizedRGFlowProducerCertificate where
  representation_physicalization :=
    ⟨su7RepresentationPhysicalizationReceipt⟩
  block_embedding_injective :=
    GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7_injective
  incidence_matter_carrier :=
    ⟨su7BlockIncidenceMatterCarrierCertificate⟩
  incidence_reconstructs_qcd_trace :=
    qcdBlockIncidenceOneLoopInput_eq_incidenceCarrierTraceInput
  anomaly_cancellation :=
    ⟨standardModelMultipletAnomalyCancellationCertificate⟩
  oriented_hypercharge_unique := by
    intro Y hc hw hg hcu he horient
    exact
      OneGenerationHyperchargeAssignment.normalized_oriented_anomaly_solution_eq_standardModel
        hc hw hg hcu he horient
  representation_qcd_b0 :=
    qcd_b0_from_final_carrier_formula
  qcd_b0_and_alpha_gap :=
    ⟨qcd_b0_from_final_carrier_formula, alphaStrongTwoLoopSMDisplayedGap_pos⟩
  qcd_inverse_flow_slope_from_representation := by
    intro sigma0 t hsigma
    rw [
      color_oneLoopSigmaFlow_inverse_linear sigma0 t hsigma,
      qcd_b0_from_final_carrier_formula]
    ring

end StandardModelConstraint
end SaturationMonoid
