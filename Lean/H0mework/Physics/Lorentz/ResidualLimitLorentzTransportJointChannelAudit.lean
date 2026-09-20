import H0mework.Physics.Lorentz.ResidualLimitLorentzSourceTransport

/-!
# S9-C3h33: joint residual support of the Lorentz transport endpoint

This audit consumes C3h32's parameter-free production endpoint reader.  It
does not reconstruct the relative coordinate, add a source slot, or accept an
endpoint witness.

At the origin, the production reader retains the actual residual-limit
curvature and every primitive field except the Lorentz connection origin.
The complete nine-channel residual therefore has the following support:

* all three algebraic coordinates agree with the reference and are zero;
* P286 connection, scalar, matter, conjugate-matter, and coframe agree with
  the reference;
* only the Lorentz-connection coordinate may differ.

Agreement with the reference is only an endpoint-delta statement.  For
`K = 1 - sigma`, an unchanged coordinate has transport defect `sigma • r`.
It is therefore transported only when that reference coordinate is zero.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzTransportJointChannelAudit

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineConjugateMatterVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterPointwiseEquation
open StageNineP286GaugeConnectionActionVariation
open StageNineConnectionSectorSourceBalance
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzSourceTransport
open DiracExteriorMatterAction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 100000

/-! ## Production endpoint aliases -/

/-- Audit alias of C3h32's parameter-free endpoint reader. -/
abbrev jointAuditEndpointReader : StageNineHolonomicConfiguration :=
  residualLimitRequiredTransportReader

/-- Audit alias of C3h32's uniquely forced relative coordinate. -/
abbrev jointAuditQStar : LorentzBivectorOneForm :=
  residualLimitRequiredTransportRelativeOrigin

theorem jointAuditEndpointReader_eq_qStarReader :
    jointAuditEndpointReader =
      residualLimitRelativeOriginReader jointAuditQStar :=
  rfl

/-! ## Origin point-field equality -/

theorem jointAuditEndpointReader_matterCovariantDerivative_origin :
    holonomicMatterCovariantDerivative jointAuditEndpointReader 0 =
      holonomicMatterCovariantDerivative residualLimitLorentzCarrierReader 0 := by
  funext direction
  have endpointDerivative :
      fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv
            (jointAuditEndpointReader.matter candidate))
          0 direction = 0 := by
    change fieldDirectionalDerivative
      (fun _ : BasePoint => matterCoordinateEquiv 0) 0 direction = 0
    simp [fieldDirectionalDerivative]
  have referenceDerivative :
      fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv
            (residualLimitLorentzCarrierReader.matter candidate))
          0 direction = 0 := by
    change fieldDirectionalDerivative
      (fun _ : BasePoint => matterCoordinateEquiv 0) 0 direction = 0
    simp [fieldDirectionalDerivative]
  unfold holonomicMatterCovariantDerivative
  rw [endpointDerivative, referenceDerivative]
  rw [show jointAuditEndpointReader.matter 0 = 0 by rfl,
    show residualLimitLorentzCarrierReader.matter 0 = 0 by rfl]
  simp

/-- The primitive Lorentz connection changes, but the actual origin point
field does not: curvature is retained and the complete matter field is zero. -/
theorem jointAuditEndpointReader_pointField_origin :
    toContinuumPointField jointAuditEndpointReader 0 =
      toContinuumPointField residualLimitLorentzCarrierReader 0 := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  · change holonomicGravityCurvature jointAuditEndpointReader 0 =
      holonomicGravityCurvature residualLimitLorentzCarrierReader 0
    rw [residualLimitRequiredTransportReader_curvature_origin]
    exact (residualLimitExtension_gravityCurvature_origin
      residualLimitLorentzCarrierReader
      residualLimitLorentzCarrierReader_extends).symm
  · exact jointAuditEndpointReader_matterCovariantDerivative_origin

/-! ## Full Lorentz EL reduction to the gravity--BF balance -/

/-- A zero matter value at the audited point kills the actual exterior-matter
spin source.  This consumes the primitive matter field, not a supplied
current or a Lorentz residual receipt. -/
theorem lorentzMatterSpinSourceCoefficient_zero_of_matter_origin_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (matterOriginZero : configuration.matter 0 = 0) :
    lorentzMatterSpinSourceCoefficient source configuration direction 0 = 0 := by
  unfold lorentzMatterSpinSourceCoefficient
  unfold holonomicMatterLorentzConnectionVariation
  rw [matterOriginZero]
  simp [matterGaugeConnectionFirstVariationDensity,
    matterGaugeConnectionVariationVector, matterGaugeKineticSum]

/-! ## Actual nine-channel comparison -/

def jointAuditEndpointResidual :
    CurrentPointwiseJointShellResidualCarrier :=
  currentPointwiseJointShellResidual positiveSmoothUnifiedSource
    jointAuditEndpointReader 0

def jointAuditReferenceResidual :
    CurrentPointwiseJointShellResidualCarrier :=
  currentPointwiseJointShellResidual positiveSmoothUnifiedSource
    residualLimitLorentzCarrierReader 0

/-- A shallow field replacement used to keep the large production coordinate
opaque while auditing channels that do not consume the Lorentz connection. -/
def jointAuditReplaceGravityConnection
    (configuration : StageNineHolonomicConfiguration)
    (connection : LorentzConnectionField) : StageNineHolonomicConfiguration :=
  { configuration with gravityConnection := connection }

theorem jointAuditEndpointReader_eq_replaceGravityConnection :
    jointAuditEndpointReader =
      jointAuditReplaceGravityConnection residualLimitLorentzCarrierReader
        (residualLimitRelativeOriginConnectionField jointAuditQStar) :=
  rfl

theorem replaceGravityConnection_p286GaugeConnection_unchanged
    (configuration : StageNineHolonomicConfiguration)
    (connection : LorentzConnectionField) (point : BasePoint) :
    (currentPointwiseJointShellResidual positiveSmoothUnifiedSource
        (jointAuditReplaceGravityConnection configuration connection)
        point).eulerLagrange.p286GaugeConnection =
      (currentPointwiseJointShellResidual positiveSmoothUnifiedSource
        configuration point).eulerLagrange.p286GaugeConnection := by
  funext direction
  rfl

theorem replaceGravityConnection_scalar_unchanged
    (configuration : StageNineHolonomicConfiguration)
    (connection : LorentzConnectionField) (point : BasePoint) :
    (currentPointwiseJointShellResidual positiveSmoothUnifiedSource
        (jointAuditReplaceGravityConnection configuration connection)
        point).eulerLagrange.scalar =
      (currentPointwiseJointShellResidual positiveSmoothUnifiedSource
        configuration point).eulerLagrange.scalar := by
  funext direction
  rfl

theorem jointAudit_endpoint_algebraic_zero :
    jointAuditEndpointResidual.algebraic = 0 := by
  change currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      residualLimitRequiredTransportReader 0 = 0
  exact residualLimitRequiredTransportReader_algebraicResidual_zero

theorem jointAudit_reference_algebraic_zero :
    jointAuditReferenceResidual.algebraic = 0 := by
  change currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      residualLimitLorentzCarrierReader 0 = 0
  have zeroRelative :=
    residualLimitRelativeOriginReader_algebraicResidual_zero
      (0 : LorentzBivectorOneForm)
  rw [residualLimitRelativeOriginReader_zero] at zeroRelative
  exact zeroRelative

theorem jointAudit_algebraic_unchanged :
    jointAuditEndpointResidual.algebraic =
      jointAuditReferenceResidual.algebraic := by
  rw [jointAudit_endpoint_algebraic_zero,
    jointAudit_reference_algebraic_zero]

theorem jointAudit_p286GaugeConnection_unchanged :
    jointAuditEndpointResidual.eulerLagrange.p286GaugeConnection =
      jointAuditReferenceResidual.eulerLagrange.p286GaugeConnection := by
  unfold jointAuditEndpointResidual jointAuditReferenceResidual
  rw [jointAuditEndpointReader_eq_replaceGravityConnection]
  exact replaceGravityConnection_p286GaugeConnection_unchanged _ _ _

theorem jointAudit_scalar_unchanged :
    jointAuditEndpointResidual.eulerLagrange.scalar =
      jointAuditReferenceResidual.eulerLagrange.scalar := by
  unfold jointAuditEndpointResidual jointAuditReferenceResidual
  rw [jointAuditEndpointReader_eq_replaceGravityConnection]
  exact replaceGravityConnection_scalar_unchanged _ _ _

/-- Vanishing conjugate matter kills both matter EL terms without unfolding
the endpoint connection or trying to normalize the complete action. -/
theorem matterEulerLagrange_zero_of_conjugateMatter_zero
    (configuration : StageNineHolonomicConfiguration)
    (conjugateMatterZero : configuration.conjugateMatter = 0) :
    (fun direction =>
      matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        configuration direction 0) = 0 := by
  funext direction
  have conjugateMatterAtZero : configuration.conjugateMatter 0 = 0 := by
    rw [conjugateMatterZero]
    rfl
  have algebraicZero :
      matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
          configuration direction 0 = 0 := by
    unfold matterAlgebraicDirectionalCoefficient
    rw [conjugateMatterAtZero]
    simp
  have momentumZero (derivativeDirection : LorentzianIndex) :
      matterDifferentialMomentum positiveSmoothUnifiedSource configuration
          direction derivativeDirection = 0 := by
    funext point
    have conjugateMatterAtPoint : configuration.conjugateMatter point = 0 := by
      rw [conjugateMatterZero]
      rfl
    unfold matterDifferentialMomentum
    rw [conjugateMatterAtPoint]
    simp
  unfold matterEulerLagrangeDirectionalCoefficient
  rw [algebraicZero]
  unfold matterDifferentialMomentumDivergence
  simp_rw [momentumZero]
  simp [fieldDirectionalDerivative]

theorem jointAudit_matter_zero :
    jointAuditEndpointResidual.eulerLagrange.matter = 0 := by
  change (fun direction =>
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      jointAuditEndpointReader direction 0) = 0
  exact matterEulerLagrange_zero_of_conjugateMatter_zero
    jointAuditEndpointReader (by rfl)

theorem jointAudit_reference_matter_zero :
    jointAuditReferenceResidual.eulerLagrange.matter = 0 := by
  change (fun direction =>
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      residualLimitLorentzCarrierReader direction 0) = 0
  exact matterEulerLagrange_zero_of_conjugateMatter_zero
    residualLimitLorentzCarrierReader (by rfl)

theorem jointAudit_matter_unchanged :
    jointAuditEndpointResidual.eulerLagrange.matter =
      jointAuditReferenceResidual.eulerLagrange.matter := by
  rw [jointAudit_matter_zero, jointAudit_reference_matter_zero]

theorem jointAudit_conjugateMatter_unchanged :
    jointAuditEndpointResidual.eulerLagrange.conjugateMatter =
      jointAuditReferenceResidual.eulerLagrange.conjugateMatter := by
  funext direction
  unfold jointAuditEndpointResidual jointAuditReferenceResidual
    currentPointwiseJointShellResidual currentPointwiseEulerLagrangeResidual
    conjugateMatterDirectionalCoefficient
  rw [jointAuditEndpointReader_pointField_origin]

theorem jointAudit_coframe_unchanged :
    jointAuditEndpointResidual.eulerLagrange.coframe =
      jointAuditReferenceResidual.eulerLagrange.coframe := by
  unfold jointAuditEndpointResidual jointAuditReferenceResidual
    currentPointwiseJointShellResidual currentPointwiseEulerLagrangeResidual
  rw [jointAuditEndpointReader_pointField_origin]

theorem jointAuditEndpointReader_lorentzMatterSpinSource_origin_zero
    (direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        jointAuditEndpointReader direction 0 = 0 :=
  lorentzMatterSpinSourceCoefficient_zero_of_matter_origin_zero
    positiveSmoothUnifiedSource jointAuditEndpointReader direction (by rfl)

theorem jointAuditReferenceReader_lorentzMatterSpinSource_origin_zero
    (direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        residualLimitLorentzCarrierReader direction 0 = 0 :=
  lorentzMatterSpinSourceCoefficient_zero_of_matter_origin_zero
    positiveSmoothUnifiedSource residualLimitLorentzCarrierReader direction
      (by rfl)

theorem jointAuditEndpointReader_lorentzEuler_eq_gravityBFBalance :
    (fun direction =>
      lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        jointAuditEndpointReader direction 0) =
      (fun direction =>
        lorentzGravityBFBalanceCoefficient jointAuditEndpointReader
          direction 0) := by
  funext direction
  rw [lorentzConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    jointAuditEndpointReader_lorentzMatterSpinSource_origin_zero]
  ring

theorem jointAuditReferenceReader_lorentzEuler_eq_gravityBFBalance :
    (fun direction =>
      lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        residualLimitLorentzCarrierReader direction 0) =
      (fun direction =>
        lorentzGravityBFBalanceCoefficient residualLimitLorentzCarrierReader
          direction 0) := by
  funext direction
  rw [lorentzConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    jointAuditReferenceReader_lorentzMatterSpinSource_origin_zero]
  ring

/-- C3h32 transports the actual complete Lorentz EL residual, not merely its
gravity--BF readout: the only additional sector is the matter spin source,
which vanishes from the retained zero matter field at the origin. -/
theorem jointAudit_lorentzEuler_transport :
    (fun direction =>
      lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        jointAuditEndpointReader direction 0) =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        (fun direction =>
          lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
            residualLimitLorentzCarrierReader direction 0) := by
  rw [jointAuditEndpointReader_lorentzEuler_eq_gravityBFBalance,
    jointAuditReferenceReader_lorentzEuler_eq_gravityBFBalance]
  change (fun direction =>
      lorentzGravityBFBalanceCoefficient
        residualLimitRequiredTransportReader direction 0) =
    (1 - positiveSmoothUnifiedSource.legacy.sigma) •
      (fun direction =>
        lorentzGravityBFBalanceCoefficient residualLimitLorentzCarrierReader
          direction 0)
  have transport := residualLimitRequiredTransportReader_gravityBFBalance
  change (fun direction =>
      lorentzGravityBFBalanceCoefficient
        residualLimitRequiredTransportReader direction 0) =
    (1 - positiveSmoothUnifiedSource.legacy.sigma) •
      (fun direction =>
        lorentzGravityBFBalanceCoefficient residualLimitLorentzCarrierReader
          direction 0) at transport
  exact transport

theorem jointAuditEndpointResidual_lorentzConnection_transport :
    jointAuditEndpointResidual.eulerLagrange.lorentzConnection =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        jointAuditReferenceResidual.eulerLagrange.lorentzConnection := by
  change (fun direction =>
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
      jointAuditEndpointReader direction 0) = _
  exact jointAudit_lorentzEuler_transport

/-- Complete non-Lorentz support classification.  The algebraic equality is
the equality of all three algebraic coordinates; the remaining five
conjuncts exhaust every EL coordinate except the Lorentz connection. -/
theorem jointAudit_complete_nonLorentz_support :
    jointAuditEndpointResidual.algebraic =
        jointAuditReferenceResidual.algebraic ∧
      jointAuditEndpointResidual.eulerLagrange.p286GaugeConnection =
        jointAuditReferenceResidual.eulerLagrange.p286GaugeConnection ∧
      jointAuditEndpointResidual.eulerLagrange.scalar =
        jointAuditReferenceResidual.eulerLagrange.scalar ∧
      jointAuditEndpointResidual.eulerLagrange.matter =
        jointAuditReferenceResidual.eulerLagrange.matter ∧
      jointAuditEndpointResidual.eulerLagrange.conjugateMatter =
        jointAuditReferenceResidual.eulerLagrange.conjugateMatter ∧
      jointAuditEndpointResidual.eulerLagrange.coframe =
        jointAuditReferenceResidual.eulerLagrange.coframe :=
  ⟨jointAudit_algebraic_unchanged,
    jointAudit_p286GaugeConnection_unchanged,
    jointAudit_scalar_unchanged,
    jointAudit_matter_unchanged,
    jointAudit_conjugateMatter_unchanged,
    jointAudit_coframe_unchanged⟩

/-! ## Unchanged coordinates still carry transport responsibility -/

/-- If an endpoint coordinate is unchanged, subtracting the required keep
reveals exactly the complementary `sigma • reference` responsibility. -/
theorem unchanged_minus_keep_eq_sigma_smul
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (endpoint reference : V) (unchanged : endpoint = reference) :
    endpoint - (1 - positiveSmoothUnifiedSource.legacy.sigma) • reference =
      positiveSmoothUnifiedSource.legacy.sigma • reference := by
  rw [unchanged]
  module

theorem unchanged_minus_keep_ne_zero_of_reference_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (endpoint reference : V) (unchanged : endpoint = reference)
    (referenceNe : reference ≠ 0) :
    endpoint - (1 - positiveSmoothUnifiedSource.legacy.sigma) • reference ≠ 0 := by
  rw [unchanged_minus_keep_eq_sigma_smul endpoint reference unchanged]
  exact smul_ne_zero
    (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos) referenceNe

theorem jointAudit_qStar_p286GaugeConnection_minus_keep :
    jointAuditEndpointResidual.eulerLagrange.p286GaugeConnection -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          jointAuditReferenceResidual.eulerLagrange.p286GaugeConnection =
      positiveSmoothUnifiedSource.legacy.sigma •
        jointAuditReferenceResidual.eulerLagrange.p286GaugeConnection :=
  unchanged_minus_keep_eq_sigma_smul _ _
    jointAudit_p286GaugeConnection_unchanged

theorem jointAudit_qStar_scalar_minus_keep :
    jointAuditEndpointResidual.eulerLagrange.scalar -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          jointAuditReferenceResidual.eulerLagrange.scalar =
      positiveSmoothUnifiedSource.legacy.sigma •
        jointAuditReferenceResidual.eulerLagrange.scalar :=
  unchanged_minus_keep_eq_sigma_smul _ _ jointAudit_scalar_unchanged

theorem jointAudit_qStar_matter_minus_keep :
    jointAuditEndpointResidual.eulerLagrange.matter -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          jointAuditReferenceResidual.eulerLagrange.matter =
      positiveSmoothUnifiedSource.legacy.sigma •
        jointAuditReferenceResidual.eulerLagrange.matter :=
  unchanged_minus_keep_eq_sigma_smul _ _ jointAudit_matter_unchanged

theorem jointAudit_qStar_conjugateMatter_minus_keep :
    jointAuditEndpointResidual.eulerLagrange.conjugateMatter -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          jointAuditReferenceResidual.eulerLagrange.conjugateMatter =
      positiveSmoothUnifiedSource.legacy.sigma •
        jointAuditReferenceResidual.eulerLagrange.conjugateMatter :=
  unchanged_minus_keep_eq_sigma_smul _ _
    jointAudit_conjugateMatter_unchanged

theorem jointAudit_qStar_coframe_minus_keep :
    jointAuditEndpointResidual.eulerLagrange.coframe -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          jointAuditReferenceResidual.eulerLagrange.coframe =
      positiveSmoothUnifiedSource.legacy.sigma •
        jointAuditReferenceResidual.eulerLagrange.coframe :=
  unchanged_minus_keep_eq_sigma_smul _ _ jointAudit_coframe_unchanged

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzTransportJointChannelAudit
