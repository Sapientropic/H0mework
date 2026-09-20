import H0mework.Physics.GaugeAction.QStarP286JointProjectionTransport

/-!
# S9-C3h58: q-star/P286 gauge projection transport

C3h57 constructed the exact-lineage q-star/P286 connection update and closed
its three algebraic and Lorentz projections.  This narrow continuation proves
that the actual P286 Euler--Lagrange projection is exactly C3h41's unique keep
endpoint and obeys `r' = (1 - sigma) r`.

The scalar and matter currents used in this equation are expanded from the
actual endpoint fields and vanish there.  The nonzero endpoint responsibility
itself remains C3h41's already-proved no-third-sink result; this module does
not repackage it through an expensive whole-function probe theorem.

No target residual, endpoint witness, branch receipt, whole point-field
equality, stationarity, or coframe transport law is accepted or asserted.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineQStarP286GaugeProjectionTransport

open ProofFreeRicherAnholonomicSource
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineP286ColorMixingOriginResidualTransport
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineQStarP286JointProjectionTransport
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzSourceTransport
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## P286 connection projection -/

theorem qStarP286Endpoint_coframe_eq_colorMixing :
    qStarP286EndpointReader.coframe =
      (colorMixingOriginConfiguration
        colorMixingOriginActualKeepEndpointParameter).coframe :=
  rfl

theorem qStarP286Endpoint_gaugeConnection_eq_colorMixing :
    qStarP286EndpointReader.gaugeConnection =
      (colorMixingOriginConfiguration
        colorMixingOriginActualKeepEndpointParameter).gaugeConnection :=
  rfl

theorem qStarP286Endpoint_gaugeAuxiliary_eq_colorMixing :
    qStarP286EndpointReader.gaugeAuxiliary =
      (colorMixingOriginConfiguration
        colorMixingOriginActualKeepEndpointParameter).gaugeAuxiliary :=
  rfl

theorem qStarP286Endpoint_volumeDensity_eq_colorMixing (point : BasePoint) :
    generatedVolumeDensity
        (toContinuumPointField qStarP286EndpointReader point) =
      generatedVolumeDensity
        (toContinuumPointField
          (colorMixingOriginConfiguration
            colorMixingOriginActualKeepEndpointParameter) point) := by
  unfold generatedVolumeDensity
  change abs (Matrix.det (qStarP286EndpointReader.coframe point)) =
    abs (Matrix.det
      ((colorMixingOriginConfiguration
        colorMixingOriginActualKeepEndpointParameter).coframe point))
  rw [qStarP286Endpoint_coframe_eq_colorMixing]

theorem qStarP286Endpoint_gaugeAuxiliaryCoordinate_eq_colorMixing
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate qStarP286EndpointReader point =
      holonomicP286GaugeAuxiliaryCoordinate
        (colorMixingOriginConfiguration
          colorMixingOriginActualKeepEndpointParameter) point := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [qStarP286Endpoint_gaugeAuxiliary_eq_colorMixing]

theorem qStarP286Endpoint_gaugeConnectionCoordinate_eq_colorMixing
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate qStarP286EndpointReader point =
      holonomicP286GaugeConnectionCoordinate
        (colorMixingOriginConfiguration
          colorMixingOriginActualKeepEndpointParameter) point := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [qStarP286Endpoint_gaugeConnection_eq_colorMixing]

theorem qStarP286Endpoint_algebraicCurvatureDirection_eq_colorMixing
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurvatureDirection
        qStarP286EndpointReader direction point =
      p286GaugeConnectionAlgebraicCurvatureDirection
        (colorMixingOriginConfiguration
          colorMixingOriginActualKeepEndpointParameter) direction point := by
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
  rw [qStarP286Endpoint_gaugeConnectionCoordinate_eq_colorMixing]

theorem qStarP286Endpoint_p286BFAlgebraic_eq_colorMixing
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFAlgebraicCoefficient qStarP286EndpointReader direction point =
      p286GaugeBFAlgebraicCoefficient
        (colorMixingOriginConfiguration
          colorMixingOriginActualKeepEndpointParameter) direction point := by
  unfold p286GaugeBFAlgebraicCoefficient
  rw [qStarP286Endpoint_volumeDensity_eq_colorMixing,
    qStarP286Endpoint_coframe_eq_colorMixing,
    qStarP286Endpoint_gaugeAuxiliaryCoordinate_eq_colorMixing,
    qStarP286Endpoint_algebraicCurvatureDirection_eq_colorMixing]

theorem qStarP286Endpoint_p286BFDifferentialMomentum_eq_colorMixing
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum qStarP286EndpointReader direction =
      p286GaugeConnectionBFDifferentialMomentum
        (colorMixingOriginConfiguration
          colorMixingOriginActualKeepEndpointParameter) direction := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentum
  rw [qStarP286Endpoint_volumeDensity_eq_colorMixing,
    qStarP286Endpoint_coframe_eq_colorMixing,
    qStarP286Endpoint_gaugeAuxiliaryCoordinate_eq_colorMixing]

theorem qStarP286Endpoint_p286BFDivergence_eq_colorMixing
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        qStarP286EndpointReader direction point =
      p286GaugeConnectionBFDifferentialMomentumDivergence
        (colorMixingOriginConfiguration
          colorMixingOriginActualKeepEndpointParameter) direction point := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [qStarP286Endpoint_p286BFDifferentialMomentum_eq_colorMixing]

theorem qStarP286Endpoint_p286BFBalance_eq_colorMixing
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFBalanceCoefficient qStarP286EndpointReader direction point =
      p286GaugeBFBalanceCoefficient
        (colorMixingOriginConfiguration
          colorMixingOriginActualKeepEndpointParameter) direction point := by
  unfold p286GaugeBFBalanceCoefficient
  rw [qStarP286Endpoint_p286BFAlgebraic_eq_colorMixing,
    qStarP286Endpoint_p286BFDivergence_eq_colorMixing]

theorem qStarP286Endpoint_p286ScalarCurrent_zero
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        qStarP286EndpointReader direction 0 = 0 := by
  unfold p286ScalarCurrentCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeZero :
      (toContinuumPointField
        qStarP286EndpointReader 0).scalarCovariantDerivative = 0 := by
    funext derivativeDirection
    change holonomicScalarCovariantDerivative
      (colorMixingOriginConfiguration
        colorMixingOriginActualKeepEndpointParameter) 0
        derivativeDirection = 0
    exact colorMixingOriginScalarCovariantDerivative_origin_eq_zero
      colorMixingOriginActualKeepEndpointParameter derivativeDirection
  rw [covariantDerivativeZero]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem qStarP286Endpoint_p286MatterCurrent_zero
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        qStarP286EndpointReader direction 0 = 0 := by
  unfold p286MatterCurrentCoefficient
    matterGaugeConnectionFirstVariationDensity
  have conjugateZero :
      (toContinuumPointField qStarP286EndpointReader 0).conjugateMatter = 0 :=
    rfl
  rw [conjugateZero]
  simp [matterDualFrameRelative]

theorem qStarP286Endpoint_p286GaugeConnection_eq_actualEndpoint :
    qStarP286EndpointResidual.eulerLagrange.p286GaugeConnection =
      colorMixingOriginP286Residual
        colorMixingOriginActualKeepEndpointParameter := by
  funext direction
  change p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
      qStarP286EndpointReader direction 0 =
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
      (colorMixingOriginConfiguration
        colorMixingOriginActualKeepEndpointParameter) direction 0
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    qStarP286Endpoint_p286BFBalance_eq_colorMixing,
    qStarP286Endpoint_p286ScalarCurrent_zero,
    qStarP286Endpoint_p286MatterCurrent_zero]
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    colorMixingOriginP286ScalarCurrent_eq_zero,
    colorMixingOriginP286MatterCurrent_eq_zero]

theorem qStarP286Source_p286GaugeConnection_eq_colorMixingSource :
    qStarP286SourceResidual.eulerLagrange.p286GaugeConnection =
      colorMixingOriginP286Residual (1 / 2 : ℝ) := by
  have sourceConfiguration := congrArg
    (fun configuration : StageNineHolonomicConfiguration =>
      (currentPointwiseJointShellResidual positiveSmoothUnifiedSource
        configuration 0).eulerLagrange.p286GaugeConnection)
    colorMixingOriginConfiguration_source
  exact sourceConfiguration.symm.trans (by rfl)

theorem qStarP286Endpoint_p286GaugeConnection_transport :
    qStarP286EndpointResidual.eulerLagrange.p286GaugeConnection =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        qStarP286SourceResidual.eulerLagrange.p286GaugeConnection := by
  calc
    qStarP286EndpointResidual.eulerLagrange.p286GaugeConnection =
        colorMixingOriginP286Residual
          colorMixingOriginActualKeepEndpointParameter :=
      qStarP286Endpoint_p286GaugeConnection_eq_actualEndpoint
    _ = (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        colorMixingOriginP286Residual (1 / 2 : ℝ) := by
      unfold colorMixingOriginActualKeepEndpointParameter
      exact colorMixingOriginP286Residual_transport (1 / 2 : ℝ)
    _ = (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        qStarP286SourceResidual.eulerLagrange.p286GaugeConnection :=
      congrArg ((1 - positiveSmoothUnifiedSource.legacy.sigma) • ·)
        qStarP286Source_p286GaugeConnection_eq_colorMixingSource.symm

end

end SaturationMonoid.PhysicsCore.StageNineQStarP286GaugeProjectionTransport
