import H0mework.Physics.GaugeAction.QStarP286ScalarProjectionTransport
import H0mework.Physics.Matter.ResidualLimitConjugateMatterJointChannelAudit

/-!
# S9-C3h60: q-star/P286 matter projection transport

This final narrow continuation evaluates the actual matter and
conjugate-matter equations on the exact q-star/P286 endpoint.  Primitive zero
matter forces the generated covariant derivative and Dirac--Yukawa vector to
zero, so both endpoint coordinates obey the same source keep law.

Together C3h57--C3h60 close all eight non-coframe coordinates of the current
joint residual carrier.  The coframe equation is deliberately retained as an
explicit computed obligation.  No whole residual equality, coframe receipt,
stationarity premise, branch choice, or final Stage-9 credential is asserted.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineQStarP286MatterProjectionTransport

open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineMatterPointwiseEquation
open StageNineQStarP286GaugeProjectionTransport
open StageNineQStarP286JointProjectionTransport
open StageNineQStarP286ScalarProjectionTransport
open StageNineResidualLimitConjugateMatterJointChannelAudit
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzTransportJointChannelAudit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Matter and conjugate-matter projections -/

theorem qStarP286Endpoint_matter_zero :
    qStarP286EndpointResidual.eulerLagrange.matter = 0 := by
  change (fun direction =>
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      qStarP286EndpointReader direction 0) = 0
  exact matterEulerLagrange_zero_of_conjugateMatter_zero
    qStarP286EndpointReader (by rfl)

theorem qStarP286Endpoint_matterCovariantDerivative_zero :
    holonomicMatterCovariantDerivative qStarP286EndpointReader 0 = 0 :=
  holonomicMatterCovariantDerivative_zero_of_matter_eq_zero
    qStarP286EndpointReader (by rfl)

theorem qStarP286Endpoint_generatedMatterVector_zero :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField qStarP286EndpointReader 0) = 0 :=
  generatedContinuumMatterVector_zero_of_matter_and_derivative_zero
    positiveSmoothUnifiedSource qStarP286EndpointReader (by rfl)
      qStarP286Endpoint_matterCovariantDerivative_zero

theorem qStarP286Endpoint_conjugateMatter_zero :
    qStarP286EndpointResidual.eulerLagrange.conjugateMatter = 0 := by
  change (fun direction =>
    conjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
      qStarP286EndpointReader direction 0) = 0
  exact conjugateMatterDirectionalCoefficient_zero_of_vector_zero
    positiveSmoothUnifiedSource qStarP286EndpointReader
      qStarP286Endpoint_generatedMatterVector_zero

theorem qStarP286Source_matter_zero :
    qStarP286SourceResidual.eulerLagrange.matter = 0 := by
  change jointAuditReferenceResidual.eulerLagrange.matter = 0
  exact jointAudit_reference_matter_zero

theorem qStarP286Source_conjugateMatter_zero :
    qStarP286SourceResidual.eulerLagrange.conjugateMatter = 0 := by
  change jointAuditReferenceResidual.eulerLagrange.conjugateMatter = 0
  exact jointAuditReference_conjugateMatterResidual_zero

theorem qStarP286Endpoint_matter_transport :
    qStarP286EndpointResidual.eulerLagrange.matter =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        qStarP286SourceResidual.eulerLagrange.matter := by
  rw [qStarP286Endpoint_matter_zero, qStarP286Source_matter_zero, smul_zero]

theorem qStarP286Endpoint_conjugateMatter_transport :
  qStarP286EndpointResidual.eulerLagrange.conjugateMatter =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        qStarP286SourceResidual.eulerLagrange.conjugateMatter := by
  rw [qStarP286Endpoint_conjugateMatter_zero,
    qStarP286Source_conjugateMatter_zero, smul_zero]

/-! ## Remaining coframe hard gate -/

/-- The exact remaining coframe equation of the physical lift.  It is a
computed proposition about the actual endpoint and source readouts, not a
receipt stored in either source or configuration. -/
def QStarP286CoframeTransportObligation : Prop :=
  qStarP286EndpointResidual.eulerLagrange.coframe =
    (1 - positiveSmoothUnifiedSource.legacy.sigma) •
      qStarP286SourceResidual.eulerLagrange.coframe

end

end SaturationMonoid.PhysicsCore.StageNineQStarP286MatterProjectionTransport
