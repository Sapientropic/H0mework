import H0mework.Physics.Lie.P286
import H0mework.Physics.YukawaSources.P522

/-!
# Proposition 523: conditional reference-SM finite receipt

The SU(7) representation side had become spread across several proof files:

* P286 constructs the concrete `diag(C,W,z,z⁻¹)` embedding
  `SU(3) × SU(2) × U(1) ↪ SU(7)`;
* P457 proves anomaly cancellation for the finite
  `(Q,uᶜ,dᶜ,L,eᶜ)` Weyl-multiplet carrier;
* P458 proves that the normalized anomaly equations force the Standard-Model
  hypercharge branch, up to the expected `uᶜ/dᶜ` exchange, and an orientation
  condition selects the conventional branch;
* P459/P461 connect the SU(7) block-incidence carrier to the one-loop QCD
  `b0 = 7` receipt.

This file packages those finite results as one **conditional reference-SM
receipt**.

Boundary: the structure has no field proving that the actual P286 adjoint
action restricts to the chosen P459/P508 matter schedule or induces P458's
hypercharges.  The Stage-7 Phase-0 audit proves that the current action does
not do so.  Thus the bundled embedding, chosen incidence table, anomaly
arithmetic, and `b0` arithmetic remain internally correct, but this receipt is
not an SU(7)-generated matter-spectrum producer.  It is a reference receipt
for comparison until a new representation supplies the missing restriction
theorem.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- A compact conditional/reference receipt for the finite block-incidence,
anomaly, and running arithmetic.  The legacy type name is retained to avoid
invalidating its internally correct finite consumers. -/
structure SU7RepresentationPhysicalizationReceipt where
  breaking_chain :
    GaugeProjection.SU7StandardModelBreakingChainCertificate
  breaking_chain_is_concrete :
    breaking_chain =
      GaugeProjection.ConcreteBlockDiagonal.concreteSU7BreakingChainCertificate
  block_embedding_injective :
    Function.Injective
      GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7
  matter_carrier :
    RunningSigmaBeta.SU7BlockIncidenceMatterCarrierCertificate
  anomaly_cancellation :
    RunningSigmaBeta.StandardModelMultipletAnomalyCancellationCertificate
  oriented_hypercharge_unique :
    ∀ Y : RunningSigmaBeta.OneGenerationHyperchargeAssignment,
      Y.colorAnomalyFree ->
      Y.weakAnomalyFree ->
      Y.gravitationalAnomalyFree ->
      Y.cubicAnomalyFree ->
      Y.e = 1 ->
      Y.u < Y.d ->
      Y = RunningSigmaBeta.OneGenerationHyperchargeAssignment.standardModel
  qcd_b0 :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7
  alpha_residual_necessity :
    AlphaStrongResidualNecessityReceipt

/-- THEOREM 1: the conditional reference receipt is inhabited by the concrete
block embedding and the independently established reference-SM finite
certificates.  Inhabitation does not connect the P286 action to the chosen
matter schedule. -/
noncomputable def referenceSMRepresentationPhysicalizationReceipt :
    SU7RepresentationPhysicalizationReceipt where
  breaking_chain :=
    GaugeProjection.ConcreteBlockDiagonal.concreteSU7BreakingChainCertificate
  breaking_chain_is_concrete := rfl
  block_embedding_injective :=
    GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7_injective
  matter_carrier :=
    RunningSigmaBeta.su7BlockIncidenceMatterCarrierCertificate
  anomaly_cancellation :=
    RunningSigmaBeta.standardModelMultipletAnomalyCancellationCertificate
  oriented_hypercharge_unique := by
    intro Y hc hw hg hcu he horient
    exact
      RunningSigmaBeta.OneGenerationHyperchargeAssignment.normalized_oriented_anomaly_solution_eq_standardModel
        hc hw hg hcu he horient
  qcd_b0 := RunningSigmaBeta.qcdCarrierB0FinalReceipt.beta_formula
  alpha_residual_necessity := alphaStrongResidualNecessityReceipt

/-- Compatibility name for existing finite-arithmetic consumers.  Its
semantics are the conditional/reference semantics above. -/
noncomputable abbrev su7RepresentationPhysicalizationReceipt :
    SU7RepresentationPhysicalizationReceipt :=
  referenceSMRepresentationPhysicalizationReceipt

namespace SU7RepresentationPhysicalizationReceipt

/-- THEOREM 2: the reference receipt exposes the concrete block embedding as
an injective embedding into `SU(7)`. -/
theorem concrete_block_embedding_injective
    (R : SU7RepresentationPhysicalizationReceipt) :
    Function.Injective
      GaugeProjection.ConcreteBlockDiagonal.blockDiagonalFin7 :=
  R.block_embedding_injective

/-- THEOREM 3: conditional on the reference anomaly predicates, the receipt
exposes that the oriented equations force the Standard-Model branch. -/
theorem oriented_anomalies_force_standardModel
    (R : SU7RepresentationPhysicalizationReceipt)
    (Y : RunningSigmaBeta.OneGenerationHyperchargeAssignment)
    (hc : Y.colorAnomalyFree)
    (hw : Y.weakAnomalyFree)
    (hg : Y.gravitationalAnomalyFree)
    (hcu : Y.cubicAnomalyFree)
    (he : Y.e = 1)
    (horient : Y.u < Y.d) :
    Y = RunningSigmaBeta.OneGenerationHyperchargeAssignment.standardModel :=
  R.oriented_hypercharge_unique Y hc hw hg hcu he horient

/-- THEOREM 4: the reference receipt carries the internally correct QCD
one-loop coefficient `b0=7` and alpha_s residual arithmetic together. -/
theorem qcd_b0_and_alpha_residual
    (R : SU7RepresentationPhysicalizationReceipt) :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7 ∧
      0 < alphaStrongTwoLoopSMDisplayedGap ℚ :=
  ⟨R.qcd_b0, R.alpha_residual_necessity.alpha_gap_positive⟩

end SU7RepresentationPhysicalizationReceipt

end StandardModelConstraint
end SaturationMonoid
