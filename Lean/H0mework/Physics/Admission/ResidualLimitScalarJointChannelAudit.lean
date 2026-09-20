import H0mework.Physics.Lorentz.ResidualLimitLorentzTransportJointChannelAudit
import H0mework.Physics.Admission.ResidualLimitScalarBalanceClosure

/-!
# S9-C3h36: scalar closure on the C3h33 zero-matter readers

C3h35 proves the source-only scalar kinetic balance is zero.  Its packaged
reader theorem is intentionally restricted to a residual-limit matter-orbit
class.  The C3h33 reference and endpoint readers do not carry such a receipt,
so this audit returns to the actual scalar definitions instead of fabricating
`RealizesPositiveSourceMatterFirstJetOrbitAtOrigin`.

For the reference reader, the retained six primitive fields identify the
actual kinetic algebraic term and differential divergence with C3h35's
source-only balance.  The scalar is at the generated vacuum, while the
primitive matter and conjugate-matter fields are both zero, so the potential
and Yukawa terms vanish directly.  C3h33 then transports the conclusion to
the endpoint because changing only the Lorentz connection leaves the scalar
EL coordinate unchanged.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitScalarJointChannelAudit

open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineResidualLimitDifferentialChannelNormalForm
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzTransportJointChannelAudit
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitScalarBalanceClosure
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7ExteriorBreakingYukawa
open SU7MotherGaugeTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000

/-! ## Potential and Yukawa sectors without a matter-orbit receipt -/

theorem jointAuditReference_scalarPotential_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField residualLimitLorentzCarrierReader 0)
        direction = 0 :=
  residualLimitExtension_scalarPotential_origin_eq_zero
    residualLimitLorentzCarrierReader residualLimitLorentzCarrierReader_extends
      direction

/-- Zero primitive matter at the audited point kills the scalar Yukawa
variation directly.  No matter-orbit, first-jet, or stationarity receipt is
accepted. -/
theorem scalarYukawaFirstVariationDensity_zero_of_matter_origin_zero
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (matterOriginZero : configuration.matter 0 = 0) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField configuration 0) direction = 0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  change
    (configuration.conjugateMatter 0
      (chiralExteriorYukawaAction
        (scalarCoordinateEquiv.symm direction)
        (configuration.matter 0))).re = 0
  rw [matterOriginZero]
  simp [chiralExteriorYukawaAction]

theorem jointAuditReference_scalarYukawa_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField residualLimitLorentzCarrierReader 0)
        direction = 0 :=
  scalarYukawaFirstVariationDensity_zero_of_matter_origin_zero
    residualLimitLorentzCarrierReader direction (by rfl)

/-! ## Actual kinetic algebraic term -/

theorem jointAuditReference_scalarCovariantDerivative_eq_carrier
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative residualLimitLorentzCarrierReader
        point direction =
      positiveResidualLimitScalarCovariantDerivative point direction := by
  unfold holonomicScalarCovariantDerivative
    positiveResidualLimitScalarCovariantDerivative
  rfl

theorem jointAuditReference_coframe_origin_eq_one :
    (toContinuumPointField residualLimitLorentzCarrierReader 0).coframe = 1 := by
  change positiveResidualLimitSixFieldCarrier.coframe 0 = 1
  exact positiveResidualLimitSixFieldCarrier_coframe_origin_eq_one

theorem jointAuditReference_scalarCovariantDerivative_origin_eq_source
    (direction : LorentzianIndex) :
    (toContinuumPointField residualLimitLorentzCarrierReader 0).scalarCovariantDerivative
        direction =
      positiveSourceOriginScalarGaugeDerivative direction := by
  calc
    (toContinuumPointField residualLimitLorentzCarrierReader 0).scalarCovariantDerivative
          direction =
        positiveResidualLimitScalarCovariantDerivative 0 direction :=
      jointAuditReference_scalarCovariantDerivative_eq_carrier 0 direction
    _ = 0 :=
      positiveResidualLimitScalarCovariantDerivative_origin_eq_zero direction
    _ = positiveSourceOriginScalarGaugeDerivative direction :=
      (positiveSourceOriginScalarGaugeDerivative_eq_zero direction).symm

theorem jointAuditReference_gaugeConnection_origin_eq_source
    (direction : LorentzianIndex) :
    residualLimitLorentzCarrierReader.gaugeConnection 0 direction =
      sourceP286Potential positiveSmoothUnifiedSource.legacy direction := by
  change sourceP286AffineConnectionField positiveSmoothUnifiedSource.legacy
      0 direction = _
  exact sourceP286AffineConnectionField_origin _ _

theorem jointAuditReference_scalarKineticAlgebraic_origin_eq_source
    (direction : ScalarCoordinateCarrier) :
    generatedVolumeDensity
          (toContinuumPointField residualLimitLorentzCarrierReader 0) *
        scalarGaugeConnectionKineticFirstVariationDensity
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField residualLimitLorentzCarrierReader 0)
          (holonomicScalarVariationAlgebraicDirection
            residualLimitLorentzCarrierReader direction 0) =
      positiveSourceOriginScalarKineticAlgebraic direction := by
  have covariantDerivativeOrigin :
      (toContinuumPointField residualLimitLorentzCarrierReader 0).scalarCovariantDerivative =
        positiveSourceOriginScalarGaugeDerivative := by
    funext derivativeDirection
    exact jointAuditReference_scalarCovariantDerivative_origin_eq_source
      derivativeDirection
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    positiveSourceOriginScalarKineticAlgebraic
    holonomicScalarVariationAlgebraicDirection
  rw [jointAuditReference_coframe_origin_eq_one,
    covariantDerivativeOrigin]
  simp_rw [jointAuditReference_gaugeConnection_origin_eq_source]
  simp [generatedVolumeDensity, scalarFrameRelativeCovariantDerivative]
  rw [jointAuditReference_coframe_origin_eq_one, Matrix.det_one, abs_one,
    one_mul]

/-! ## Actual differential momentum and divergence -/

theorem jointAuditReference_scalarDifferentialMomentum_eq_source
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        residualLimitLorentzCarrierReader direction derivativeDirection =
      positiveResidualLimitScalarDifferentialMomentum direction
        derivativeDirection := by
  funext point
  have coframePoint :
      (toContinuumPointField residualLimitLorentzCarrierReader point).coframe =
        positiveResidualLimitSixFieldCarrier.coframe point := by
    rfl
  have scalarCovariantDerivativePoint :
      (toContinuumPointField residualLimitLorentzCarrierReader point).scalarCovariantDerivative =
        positiveResidualLimitScalarCovariantDerivative point := by
    funext formDirection
    exact jointAuditReference_scalarCovariantDerivative_eq_carrier
      point formDirection
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    positiveResidualLimitScalarDifferentialMomentum generatedVolumeDensity
  rw [coframePoint, scalarCovariantDerivativePoint]
  simp [scalarFrameRelativeCovariantDerivative]

theorem jointAuditReference_scalarDivergence_eq_source
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        residualLimitLorentzCarrierReader direction 0 =
      positiveResidualLimitScalarDivergence direction := by
  unfold scalarDifferentialMomentumDivergence
    positiveResidualLimitScalarDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  apply congrArg
    (fun momentum : BasePoint → ℝ =>
      fieldDirectionalDerivative momentum 0 derivativeDirection)
  exact jointAuditReference_scalarDifferentialMomentum_eq_source
    direction derivativeDirection

/-! ## Full scalar EL closure and transport -/

theorem jointAuditReference_scalarResidual_eq_sourceBalance
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        residualLimitLorentzCarrierReader direction 0 =
      positiveResidualLimitScalarKineticBalance direction := by
  unfold scalarEulerLagrangeDirectionalCoefficient
    scalarAlgebraicDirectionalCoefficient
  rw [jointAuditReference_scalarPotential_origin_zero,
    jointAuditReference_scalarYukawa_origin_zero]
  simp only [sub_zero, add_zero]
  rw [jointAuditReference_scalarKineticAlgebraic_origin_eq_source,
    jointAuditReference_scalarDivergence_eq_source]
  rfl

theorem jointAuditReference_scalarResidual_eq_sourceBalance_allDirections :
    (fun direction =>
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        residualLimitLorentzCarrierReader direction 0) =
      positiveResidualLimitScalarKineticBalance := by
  funext direction
  exact jointAuditReference_scalarResidual_eq_sourceBalance direction

theorem jointAuditReference_scalarResidual_zero :
    jointAuditReferenceResidual.eulerLagrange.scalar = 0 := by
  change (fun direction =>
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      residualLimitLorentzCarrierReader direction 0) = 0
  rw [jointAuditReference_scalarResidual_eq_sourceBalance_allDirections,
    positiveResidualLimitScalarKineticBalance_eq_zero]

theorem jointAuditEndpoint_scalarResidual_zero :
    jointAuditEndpointResidual.eulerLagrange.scalar = 0 := by
  rw [jointAudit_scalar_unchanged,
    jointAuditReference_scalarResidual_zero]

/-- The C3h32 endpoint now satisfies the scalar coordinate of `r' = K r`.
The proof uses actual zero residuals on both readers, not an unchanged-channel
shortcut with an unexamined reference value. -/
theorem jointAuditEndpoint_scalarResidual_transport :
    jointAuditEndpointResidual.eulerLagrange.scalar =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        jointAuditReferenceResidual.eulerLagrange.scalar := by
  rw [jointAuditEndpoint_scalarResidual_zero,
    jointAuditReference_scalarResidual_zero, smul_zero]

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitScalarJointChannelAudit
