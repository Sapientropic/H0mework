import H0mework.Physics.GaugeAction.ResidualLimitP286ScalarSourceNormalForm
import H0mework.Physics.Geometry.RequiredDifferentialResponseTransport

/-!
# S9-C3h26: frozen P286 and scalar transport boundary

The residual-limit six-field reader freezes the P286 auxiliary momentum and
the scalar differential momentum across every two extensions of that same
source carrier.  This module records the resulting exact boundary:

* actual source-only residuals can obey `r' = K r` inside the frozen class iff
  the source-only balance is already zero;
* the frozen endpoint divergence matches the C3h20 required-response readout
  iff that same initial source-only balance is zero.

These are equivalences for an explicitly supplied carrier class.  They do not
assert that the balance is nonzero, do not prove an actual no-go, and do not
generate an endpoint configuration or update.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitP286ScalarFrozenTransportBoundary

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointResidualResponseSnapshot
open StageNineRequiredDifferentialResponseTransport
open StageNineResidualLimitMatterOrbitJointClassification
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineConnectionSectorSourceBalance
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineScalarPointwiseEquation
open StageNineScalarVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Divergence invariance from the six frozen primitive fields -/

private theorem residualLimitExtensions_p286Momentum_eq
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal)
    (direction : P286GaugeTwoForm)
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum initial direction point =
      p286GaugeConnectionBFDifferentialMomentum terminal direction point := by
  have coframeEquality : initial.coframe = terminal.coframe :=
    initialExtends.coframe.trans terminalExtends.coframe.symm
  have auxiliaryEquality : initial.gaugeAuxiliary = terminal.gaugeAuxiliary :=
    initialExtends.gaugeAuxiliary.trans terminalExtends.gaugeAuxiliary.symm
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
    holonomicP286GaugeAuxiliaryCoordinate toContinuumPointField
  rw [coframeEquality, auxiliaryEquality]

/-- The P286 differential divergence is frozen by exactly two residual-limit
six-field extension receipts; no matter-orbit or index premise is needed. -/
theorem residualLimitExtensions_p286Divergence_eq
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence initial direction 0 =
      p286GaugeConnectionBFDifferentialMomentumDivergence terminal direction 0 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  apply congrArg
    (fun momentum : BasePoint → ℝ =>
      fieldDirectionalDerivative momentum 0 derivativeDirection)
  funext point
  exact residualLimitExtensions_p286Momentum_eq initial terminal
    initialExtends terminalExtends _ point

private theorem residualLimitExtensions_scalarMomentum_eq
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource initial direction
        derivativeDirection point =
      scalarDifferentialMomentum positiveSmoothUnifiedSource terminal direction
        derivativeDirection point := by
  have coframeEquality : initial.coframe = terminal.coframe :=
    initialExtends.coframe.trans terminalExtends.coframe.symm
  have gaugeConnectionEquality :
      initial.gaugeConnection = terminal.gaugeConnection :=
    initialExtends.gaugeConnection.trans terminalExtends.gaugeConnection.symm
  have scalarEquality : initial.scalar = terminal.scalar :=
    initialExtends.scalar.trans terminalExtends.scalar.symm
  have covariantDerivativeEquality :
      holonomicScalarCovariantDerivative initial point =
        holonomicScalarCovariantDerivative terminal point := by
    funext formDirection
    unfold holonomicScalarCovariantDerivative
    rw [gaugeConnectionEquality, scalarEquality]
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    generatedVolumeDensity
  rw [show (toContinuumPointField initial point).coframe =
        initial.coframe point by rfl,
    show (toContinuumPointField terminal point).coframe =
        terminal.coframe point by rfl,
    show (toContinuumPointField initial point).scalarCovariantDerivative =
        holonomicScalarCovariantDerivative initial point by rfl,
    show (toContinuumPointField terminal point).scalarCovariantDerivative =
        holonomicScalarCovariantDerivative terminal point by rfl,
    coframeEquality, covariantDerivativeEquality]

/-- The scalar differential divergence is likewise frozen by only the two
six-field extension receipts. -/
theorem residualLimitExtensions_scalarDivergence_eq
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource initial
        direction 0 =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource terminal
        direction 0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  apply congrArg
    (fun momentum : BasePoint → ℝ =>
      fieldDirectionalDerivative momentum 0 derivativeDirection)
  funext point
  exact residualLimitExtensions_scalarMomentum_eq initial terminal
    initialExtends terminalExtends direction derivativeDirection point

/-! ## Exact frozen transport boundary -/

private theorem self_eq_sourceKeep_iff_eq_zero
    {Direction : Type*}
    (sigma : ℝ)
    (sigmaNonzero : sigma ≠ 0)
    (residual : Direction → ℝ) :
    residual = (1 - sigma) • residual ↔ residual = 0 := by
  constructor
  · intro transported
    funext direction
    have pointTransport := congrFun transported direction
    change residual direction = (1 - sigma) * residual direction at pointTransport
    have productZero : sigma * residual direction = 0 := by
      linarith
    exact (mul_eq_zero.mp productZero).resolve_left sigmaNonzero
  · intro residualZero
    rw [residualZero]
    simp

private theorem frozen_eq_requiredDifferentialResponse_iff_residual_eq_zero
    {Direction : Type*}
    (sigma : ℝ)
    (sigmaNonzero : sigma ≠ 0)
    (algebraic initialDivergence terminalDivergence : Direction → ℝ)
    (frozen : terminalDivergence = initialDivergence) :
    terminalDivergence =
        requiredDifferentialResponse sigma algebraic initialDivergence ↔
      (fun direction =>
        algebraic direction - initialDivergence direction) = 0 := by
  rw [frozen]
  constructor
  · intro requiredEquality
    funext direction
    have pointEquality := congrFun requiredEquality direction
    unfold requiredDifferentialResponse at pointEquality
    have productZero :
        sigma * (algebraic direction - initialDivergence direction) = 0 := by
      linarith
    exact (mul_eq_zero.mp productZero).resolve_left sigmaNonzero
  · intro residualZero
    funext direction
    have pointZero := congrFun residualZero direction
    change algebraic direction - initialDivergence direction = 0 at pointZero
    unfold requiredDifferentialResponse
    rw [pointZero]
    ring

/-- In the frozen residual-limit and matter-orbit reader class, the actual
P286 residual satisfies the framework keep law exactly iff its source-only
balance function is zero. -/
theorem residualLimitMatterOrbit_p286ActualResidual_transport_iff_sourceBalance_zero
    (initialIndex terminalIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsResidualLimitAndMatterOrbitAt terminalIndex terminal) :
    (fun direction =>
      p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource terminal direction 0) =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (fun direction =>
            p286GaugeConnectionEulerLagrangeCoefficient
              positiveSmoothUnifiedSource initial direction 0) ↔
      positiveResidualLimitP286TotalBalance = 0 := by
  rw [residualLimitMatterOrbit_p286Residual_origin_eq_sourceOnly_allDirections
      initialIndex initial initialExtends,
    residualLimitMatterOrbit_p286Residual_origin_eq_sourceOnly_allDirections
      terminalIndex terminal terminalExtends]
  exact self_eq_sourceKeep_iff_eq_zero
    positiveSmoothUnifiedSource.legacy.sigma
    (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)
    positiveResidualLimitP286TotalBalance

/-- The actual frozen endpoint P286 divergence matches the C3h20 required
response iff the initial source-only P286 balance function is zero. -/
theorem residualLimitMatterOrbit_p286RequiredResponse_matches_iff_sourceBalance_zero
    (initialIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal) :
    (fun direction =>
      p286GaugeConnectionBFDifferentialMomentumDivergence terminal direction 0) =
        (sourceSigmaRequiredDifferentialResponseSnapshot
          positiveSmoothUnifiedSource
          (pointwiseResidualResponseSnapshot positiveSmoothUnifiedSource
            initial 0)).p286BFDifferentialMomentumDivergence ↔
      positiveResidualLimitP286TotalBalance = 0 := by
  have frozen :
      (fun direction =>
        p286GaugeConnectionBFDifferentialMomentumDivergence terminal
          direction 0) =
        fun direction =>
          p286GaugeConnectionBFDifferentialMomentumDivergence initial
            direction 0 := by
    funext direction
    exact (residualLimitExtensions_p286Divergence_eq initial terminal
      initialExtends.residualLimit terminalExtends direction).symm
  have boundary := frozen_eq_requiredDifferentialResponse_iff_residual_eq_zero
    positiveSmoothUnifiedSource.legacy.sigma
    (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)
    (fun direction =>
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource initial direction 0)
    (fun direction =>
      p286GaugeConnectionBFDifferentialMomentumDivergence initial direction 0)
    (fun direction =>
      p286GaugeConnectionBFDifferentialMomentumDivergence terminal direction 0)
    frozen
  have residualFunction :
      (fun direction =>
        p286GaugeConnectionEulerLagrangeCoefficient
          positiveSmoothUnifiedSource initial direction 0) =
        positiveResidualLimitP286TotalBalance :=
    residualLimitMatterOrbit_p286Residual_origin_eq_sourceOnly_allDirections
      initialIndex initial initialExtends
  rw [← residualFunction]
  simpa [sourceSigmaRequiredDifferentialResponseSnapshot,
    pointwiseResidualResponseSnapshot,
    p286GaugeConnectionEulerLagrangeCoefficient] using boundary

/-- The scalar source-only residual obeys the same exact frozen keep boundary. -/
theorem residualLimitMatterOrbit_scalarActualResidual_transport_iff_sourceBalance_zero
    (initialIndex terminalIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsResidualLimitAndMatterOrbitAt terminalIndex terminal) :
    (fun direction =>
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        terminal direction 0) =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (fun direction =>
            scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
              initial direction 0) ↔
      positiveResidualLimitScalarKineticBalance = 0 := by
  rw [residualLimitMatterOrbit_scalarResidual_origin_eq_sourceOnly_allDirections
      initialIndex initial initialExtends,
    residualLimitMatterOrbit_scalarResidual_origin_eq_sourceOnly_allDirections
      terminalIndex terminal terminalExtends]
  exact self_eq_sourceKeep_iff_eq_zero
    positiveSmoothUnifiedSource.legacy.sigma
    (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)
    positiveResidualLimitScalarKineticBalance

/-- The actual frozen endpoint scalar divergence matches the C3h20 required
response iff the initial source-only scalar balance function is zero. -/
theorem residualLimitMatterOrbit_scalarRequiredResponse_matches_iff_sourceBalance_zero
    (initialIndex : ℕ)
    (initial terminal : StageNineHolonomicConfiguration)
    (initialExtends :
      ExtendsResidualLimitAndMatterOrbitAt initialIndex initial)
    (terminalExtends :
      ExtendsPositiveSourceResidualLimitPartialPrimitiveCarrier terminal) :
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource terminal
        direction 0) =
        (sourceSigmaRequiredDifferentialResponseSnapshot
          positiveSmoothUnifiedSource
          (pointwiseResidualResponseSnapshot positiveSmoothUnifiedSource
            initial 0)).scalarDifferentialMomentumDivergence ↔
      positiveResidualLimitScalarKineticBalance = 0 := by
  have frozen :
      (fun direction =>
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource terminal
          direction 0) =
        fun direction =>
          scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource initial
            direction 0 := by
    funext direction
    exact (residualLimitExtensions_scalarDivergence_eq initial terminal
      initialExtends.residualLimit terminalExtends direction).symm
  have boundary := frozen_eq_requiredDifferentialResponse_iff_residual_eq_zero
    positiveSmoothUnifiedSource.legacy.sigma
    (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)
    (fun direction =>
      scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource initial
        direction 0)
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource initial
        direction 0)
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource terminal
        direction 0)
    frozen
  have residualFunction :
      (fun direction =>
        scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          initial direction 0) =
        positiveResidualLimitScalarKineticBalance :=
    residualLimitMatterOrbit_scalarResidual_origin_eq_sourceOnly_allDirections
      initialIndex initial initialExtends
  rw [← residualFunction]
  simpa [sourceSigmaRequiredDifferentialResponseSnapshot,
    pointwiseResidualResponseSnapshot,
    scalarEulerLagrangeDirectionalCoefficient] using boundary

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitP286ScalarFrozenTransportBoundary
