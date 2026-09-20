/-
  Proposition 514: finite information/matter unification core.

  P513 closes the finite block-product producer for the current
  information/matter carrier.  This file stops adding another small local
  receipt and instead bundles the current proved core into one theorem:

    * the general module-valued affine relaxation spine;
    * the single zero-target scalar spine;
    * the concrete `diag(C,W,z,z⁻¹)` embedding into `SU(7)`;
    * the information/matter current-carrier certificate;
    * the block-product producer for component multiplicities;
    * the trace-input / `b0` projection;
    * anomaly cancellation and normalized hypercharge branch uniqueness;
    * the QCD `b0 = 7` carrier receipt and its running-sigma delta law.

  Boundary: this is a finite formal-core theorem.  It still does not prove
  the physical producer for SU(7) representation breaking, the endpoint table
  from first principles, low-energy thresholds, the full mass spectrum, or an
  empirical identity between information and matter.
-/

import H0mework.Realization.Descent.P242
import H0mework.Physics.AlphaSources.P461
import H0mework.Physics.RepresentationSources.P513

namespace SaturationMonoid
namespace StandardModelConstraint
namespace InformationMatterProjection

open RunningSigmaBeta

/-! ## One bundled finite core -/

/-- A large finite-core receipt for the current proved content of the
"information = matter" / unified-relaxation track.

All fields are already proved upstream.  The point of this theorem is not to
hide producer boundaries, but to make the current core citeable as one object
instead of a long list of small receipts. -/
structure FiniteInformationMatterUnificationCoreCertificate : Prop where
  affine_relaxation_spine :
    ∀ {K E : Type*} [Field K] [AddCommGroup E] [Module K E],
      AffineRelaxation.UnifiedAffineRelaxationModuleCertificate K E
  single_zero_target_spine :
    ∀ {K : Type*} [Field K],
      SingleZeroTargetRelaxationReceipt K
  concrete_su7_embedding_exists :
    Nonempty GaugeProjection.SU7StandardModelBreakingChainCertificate
  concrete_su7_embedding_injective :
    Function.Injective GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7
  current_information_matter_carrier :
    ConcreteInformationMatterCarrierCertificate
  block_product_component_producer :
    ConcreteMatterBlockProductProducerCertificate
  trace_b0_projection :
    ∀ G : StandardModelGaugeFactor,
      betaCoeff (concreteSupportCarrierTraceInput G) = carrierB0 G
  anomaly_cancellation :
    StandardModelMultipletAnomalyCancellationCertificate
  normalized_hypercharge_two_branches :
    ∀ {Y : OneGenerationHyperchargeAssignment},
      OneGenerationHyperchargeAssignment.colorAnomalyFree Y ->
      OneGenerationHyperchargeAssignment.weakAnomalyFree Y ->
      OneGenerationHyperchargeAssignment.gravitationalAnomalyFree Y ->
      OneGenerationHyperchargeAssignment.cubicAnomalyFree Y ->
      Y.e = 1 ->
      Y = OneGenerationHyperchargeAssignment.standardModel ∨
        Y = OneGenerationHyperchargeAssignment.swappedSinglets
  oriented_hypercharge_standard_model :
    ∀ {Y : OneGenerationHyperchargeAssignment},
      OneGenerationHyperchargeAssignment.colorAnomalyFree Y ->
      OneGenerationHyperchargeAssignment.weakAnomalyFree Y ->
      OneGenerationHyperchargeAssignment.gravitationalAnomalyFree Y ->
      OneGenerationHyperchargeAssignment.cubicAnomalyFree Y ->
      Y.e = 1 ->
      Y.u < Y.d ->
      Y = OneGenerationHyperchargeAssignment.standardModel
  qcd_b0_from_carrier :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7
  qcd_running_delta :
    ∀ σ : ℝ,
      (standardModelOneLoopCarrier .colorSU3).residualSelfBumpStep σ - σ =
        -((betaCoeff qcdBlockIncidenceOneLoopInput : ℚ) : ℝ) * σ ^ 2

/-- THEOREM: current finite information/matter unification core.

This theorem is intentionally broad: it is the one-object receipt for the
current machine-checked finite core, while keeping the remaining physical
producer obligations outside the theorem statement. -/
theorem finiteInformationMatterUnificationCoreCertificate :
    FiniteInformationMatterUnificationCoreCertificate where
  affine_relaxation_spine := by
    intro K E _field _add _module
    exact AffineRelaxation.unifiedAffineRelaxationModuleCertificate
  single_zero_target_spine := by
    intro K _field
    exact singleZeroTargetRelaxationReceipt K
  concrete_su7_embedding_exists :=
    ⟨GaugeProjection.ConcreteBlockDiagonal.concreteSU7BreakingChainCertificate⟩
  concrete_su7_embedding_injective :=
    GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7_injective
  current_information_matter_carrier :=
    concreteInformationMatterCarrierCertificate
  block_product_component_producer :=
    concreteMatterBlockProductProducerCertificate
  trace_b0_projection :=
    betaCoeff_concreteSupportCarrierTraceInput_eq_carrierB0
  anomaly_cancellation :=
    standardModelMultipletAnomalyCancellationCertificate
  normalized_hypercharge_two_branches :=
    OneGenerationHyperchargeAssignment.normalized_anomaly_solution_two_branches
  oriented_hypercharge_standard_model :=
    OneGenerationHyperchargeAssignment.normalized_oriented_anomaly_solution_eq_standardModel
  qcd_b0_from_carrier :=
    qcd_b0_from_final_carrier_formula
  qcd_running_delta :=
    qcd_residualSelfBump_delta_from_final_carrier_formula

end InformationMatterProjection
end StandardModelConstraint
end SaturationMonoid
