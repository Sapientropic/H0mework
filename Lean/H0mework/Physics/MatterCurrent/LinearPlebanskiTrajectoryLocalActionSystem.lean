import H0mework.Physics.MatterCurrent.LinearPlebanskiTrajectoryRestart
import H0mework.Physics.Matter.ConjugateMatterActionTimeVelocity
import H0mework.Physics.Geometry.GravityBianchi
import H0mework.Physics.GaugeAction.P286Bianchi

/-!
# S9-C3h156: current linear-Plebanski local action system

C3h155 first generates, at every trajectory time and spatial contact, a
corrected local actual from the current primitive Cauchy state.  This module
only then reads the equations carried by that same actual:

```text
proof-free P506/L0 source
→ corrected whole-slice state U₄(τ)
→ same-action current local actual at x
→ smooth/nondegenerate holonomic germ
→ gravity simplicity and linear-Plebanski auxiliary balance
→ P286 auxiliary equation
→ gravity/P286 off-shell Bianchi identities
→ primal and adjoint matter origin equations.
```

The Lorentz connection remains the C3h153 corrected constructor
`F = ⋆ᵢB - λ`; no residual, zero-fiber witness, endpoint, inverse,
preimage, supplied response, coefficient, or branch receipt is accepted.
This is a local action-system checkpoint.  It does not claim the still-open
P286 connection, scalar, Lorentz/spin, or complete coframe Euler--Lagrange
sum, autonomous integral flow, global extension, or finite action.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiTrajectoryLocalActionSystem

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineGravityBianchi
open StageNineGravityGaugeActionLocalActualLift
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286Bianchi
open StageNinePlebanskiMultiplierVariation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiTrajectoryRestart
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSimpArgs false

/-! ## Generic current-actual laws -/

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_smooth
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
      source trajectoryTime state space).Smooth := by
  exact
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_smooth
      source
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state)
      space

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_simplicity
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    GravitySimplicityEquation
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space) := by
  intro point
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual,
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliary,
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe]
  rfl

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_auxiliaryBalance
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    let actual :=
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space
    holonomicGravityCurvature actual 0 -
          gravityInternalDualEquiv (actual.gravityAuxiliary 0) +
          actual.gravitySimplicityMultiplier 0 =
        0 := by
  exact
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliaryBalance
      source
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state)
      space

/-- Gauge curvature only reads the primitive P286 connection field.  This
small transporter avoids asking definitional equality to unfold the complete
nine-field stack when later action overlays retain that field. -/
theorem holonomicGaugeCurvature_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gaugeConnection = second.gaugeConnection)
    (point : BasePoint) :
    holonomicGaugeCurvature first point =
      holonomicGaugeCurvature second point := by
  funext pair
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [connectionEq]

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_p286AuxiliaryEquation
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    let actual :=
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space
    holonomicGaugeCurvature actual 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (actual.coframe 0))
        (actual.gaugeAuxiliary 0) := by
  simp only [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual]
  let current :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state
  let actual :=
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      source current space
  let jointActual :=
    sourceActionGeneratedJointLocalActualLift source current space
  let scalarActual :=
    sourceActionGeneratedMatterDualScalarLocalActualLift source current space
  let dualActual :=
    sourceActionGeneratedMatterDualLocalActualLift source current space
  let matterActual :=
    sourceActionGeneratedMatterLocalActualLift source current space
  let gravityGaugeActual :=
    sourceActionGeneratedGravityGaugeLocalActualLift source current space
  have retained :=
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_retainsJointPrimitiveFields
      source current space
  rcases retained with
    ⟨actualJointCoframe, _actualJointGravityAuxiliary,
      _actualJointMultiplier, actualJointGaugeConnection,
      actualJointGaugeAuxiliary, _actualJointScalar, _actualJointMatter,
      _actualJointConjugateMatter⟩
  have jointScalarCoframe :
      jointActual.coframe = scalarActual.coframe := by
    rfl
  have scalarDualCoframe :
      scalarActual.coframe = dualActual.coframe := by
    rfl
  have dualMatterCoframe :
      dualActual.coframe = matterActual.coframe := by
    rfl
  have matterGravityGaugeCoframe :
      matterActual.coframe = gravityGaugeActual.coframe := by
    rfl
  have jointScalarGaugeConnection :
      jointActual.gaugeConnection = scalarActual.gaugeConnection := by
    rfl
  have scalarDualGaugeConnection :
      scalarActual.gaugeConnection = dualActual.gaugeConnection := by
    rfl
  have dualMatterGaugeConnection :
      dualActual.gaugeConnection = matterActual.gaugeConnection := by
    rfl
  have matterGravityGaugeGaugeConnection :
      matterActual.gaugeConnection = gravityGaugeActual.gaugeConnection := by
    rfl
  have jointScalarGaugeAuxiliary :
      jointActual.gaugeAuxiliary = scalarActual.gaugeAuxiliary := by
    rfl
  have scalarDualGaugeAuxiliary :
      scalarActual.gaugeAuxiliary = dualActual.gaugeAuxiliary := by
    rfl
  have dualMatterGaugeAuxiliary :
      dualActual.gaugeAuxiliary = matterActual.gaugeAuxiliary := by
    rfl
  have matterGravityGaugeGaugeAuxiliary :
      matterActual.gaugeAuxiliary = gravityGaugeActual.gaugeAuxiliary := by
    rfl
  have coframeEq : actual.coframe = gravityGaugeActual.coframe :=
    actualJointCoframe.trans
      (jointScalarCoframe.trans
        (scalarDualCoframe.trans
          (dualMatterCoframe.trans matterGravityGaugeCoframe)))
  have connectionEq :
      actual.gaugeConnection = gravityGaugeActual.gaugeConnection :=
    actualJointGaugeConnection.trans
      (jointScalarGaugeConnection.trans
        (scalarDualGaugeConnection.trans
          (dualMatterGaugeConnection.trans
            matterGravityGaugeGaugeConnection)))
  have auxiliaryEq :
      actual.gaugeAuxiliary = gravityGaugeActual.gaugeAuxiliary :=
    actualJointGaugeAuxiliary.trans
      (jointScalarGaugeAuxiliary.trans
        (scalarDualGaugeAuxiliary.trans
          (dualMatterGaugeAuxiliary.trans
            matterGravityGaugeGaugeAuxiliary)))
  calc
    holonomicGaugeCurvature actual 0 =
        holonomicGaugeCurvature gravityGaugeActual 0 :=
      holonomicGaugeCurvature_eq_of_connection_eq
        actual gravityGaugeActual connectionEq 0
    _ =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear
              (gravityGaugeActual.coframe 0))
          (gravityGaugeActual.gaugeAuxiliary 0) := by
      exact
        sourceActionGeneratedGravityGaugeLocalActualLift_p286AuxiliaryEquation_origin
          source current space
    _ =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear (actual.coframe 0))
          (actual.gaugeAuxiliary 0) := by
      rw [coframeEq, auxiliaryEq]

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_gravityBianchi
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    let actual :=
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space
    covariantMixedCurvatureDerivative actual point first second third +
        covariantMixedCurvatureDerivative actual point second third first +
        covariantMixedCurvatureDerivative actual point third first second =
      0 := by
  exact
    holonomicGravityGL4Curvature_bianchi
      _
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_smooth
        source trajectoryTime state space)
      point first second third

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_p286Bianchi
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    let actual :=
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space
    covariantCurvatureDerivative actual point first second third +
        covariantCurvatureDerivative actual point second third first +
        covariantCurvatureDerivative actual point third first second =
      0 := by
  exact
    holonomicP286GaugeCurvature_bianchi
      _
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_smooth
        source trajectoryTime state space)
      point first second third

/-! ## Matter equations on the corrected origin connection -/

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_matterCovariantDerivative_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        0 direction =
      holonomicMatterCovariantDerivative
        (sourceActionGeneratedMatterLocalActualLift source
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
            source trajectoryTime state)
          space)
        0 direction := by
  let current :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state
  have matterField :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space).matter =
        (sourceActionGeneratedMatterLocalActualLift source current
          space).matter := by
    rfl
  have gravityConnectionOrigin :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space).gravityConnection 0 =
        (sourceActionGeneratedMatterLocalActualLift source current
          space).gravityConnection 0 := by
    rw [
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual,
      sourceActionGeneratedLinearPlebanskiJointLocalActualLift_initialConnection]
    exact
      (sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
        source current space).symm
  have gaugeConnectionOrigin :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
        source trajectoryTime state space).gaugeConnection 0 =
        (sourceActionGeneratedMatterLocalActualLift source current
          space).gaugeConnection 0 := by
    rfl
  unfold holonomicMatterCovariantDerivative
  rw [matterField, gravityConnectionOrigin, gaugeConnectionOrigin]

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_diracYukawa_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1) :
    generatedContinuumMatterVector source 0 0
      (toContinuumPointField
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        0) =
      0 := by
  let current :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state
  let corrected :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
      source trajectoryTime state space
  let matterActual :=
    sourceActionGeneratedMatterLocalActualLift source current space
  have coframeOrigin :
      corrected.coframe 0 = matterActual.coframe 0 := by
    rfl
  have scalarOrigin :
      corrected.scalar 0 = matterActual.scalar 0 := by
    change
      (sourceActionGeneratedMatterDualScalarLocalActualLift source current
          space).scalar 0 =
        (sourceActionGeneratedMatterLocalActualLift source current
          space).scalar 0
    rw [sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin]
    change
      current.scalar space =
        (sourceGeneratedP286ActionLocalActualLift source current
          space).scalar 0
    exact
      (sourceGeneratedP286ActionLocalActualLift_scalar_origin
        source current space).symm
  have matterOrigin :
      corrected.matter 0 = matterActual.matter 0 := by
    rfl
  have covariantDerivativeOrigin :
      ∀ direction,
        holonomicMatterCovariantDerivative corrected 0 direction =
          holonomicMatterCovariantDerivative matterActual 0 direction := by
    intro direction
    exact
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_matterCovariantDerivative_origin
        source trajectoryTime state space direction
  have covariantDerivativeOriginFun :
      holonomicMatterCovariantDerivative corrected 0 =
        holonomicMatterCovariantDerivative matterActual 0 := by
    funext direction
    exact covariantDerivativeOrigin direction
  have base :=
    sourceActionGeneratedMatterLocalActualLift_diracYukawa_origin
      source current space identityCoframe
  unfold generatedContinuumMatterVector
  simp only [toContinuumPointField]
  rw [coframeOrigin, scalarOrigin, matterOrigin]
  rw [covariantDerivativeOriginFun]
  exact base

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_variationConnection_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    holonomicMatterVariationAlgebraicDirection
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        direction 0 formDirection =
      cauchyMatterVariationConnectionOperator
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state)
        space formDirection
        (matterCoordinateEquiv.symm direction) := by
  let current :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state
  unfold holonomicMatterVariationAlgebraicDirection
    cauchyMatterVariationConnectionOperator
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual,
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_initialConnection]
  rw [show
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      source current space).gaugeConnection 0 =
        current.gaugeConnection space by
    funext candidate
    exact
      sourceGeneratedP286ActionLocalConnection_origin
        source current space candidate]
  rfl

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_algebraicVector_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicVariationVector source
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        direction 0 =
      actionGeneratedMatterAlgebraicOperator
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state)
        space (matterCoordinateEquiv.symm direction) := by
  let current :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state
  let actual :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
      source trajectoryTime state space
  unfold matterAlgebraicVariationVector matterFieldVariationVector
    actionGeneratedMatterAlgebraicOperator
  rw [matterGaugeKineticSum_zeroChart]
  simp only [toContinuumPointField]
  rw [show actual.coframe 0 = (1 : LorentzianCoframe) by
    change current.coframe space = 1
    exact identityCoframe]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp_rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_variationConnection_origin]
  rw [show actual.scalar 0 = current.scalar space by
    change
      (sourceActionGeneratedMatterDualScalarLocalActualLift source current
        space).scalar 0 = current.scalar space
    exact
      sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin
        source current space]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]
  rfl

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_differentialMomentum
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        direction derivativeDirection =
      fun point =>
        ((sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
            source trajectoryTime state space).conjugateMatter point
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  funext point
  let current :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state
  let actual :=
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
      source trajectoryTime state space
  unfold matterDifferentialMomentum matterDifferentialVariationVector
  simp only [toContinuumPointField]
  rw [show actual.coframe point = (1 : LorentzianCoframe) by
    change current.coframe space = 1
    exact identityCoframe]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by rfl]
  rw [inverseCoframeDiracGamma_identity]
  simp [generatedVolumeDensity, identityCoframeMatterPrincipal]

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_momentumDerivative_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum source
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
            source trajectoryTime state space)
          direction derivativeDirection)
        0 derivativeDirection =
      (actionGeneratedConjugateMatterLocalJet
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state)
        space derivativeDirection
        (identityCoframeMatterPrincipal derivativeDirection
          (matterCoordinateEquiv.symm direction))).re := by
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_differentialMomentum
      source trajectoryTime state space identityCoframe direction
        derivativeDirection]
  exact
    actionGeneratedConjugateMatterLocalField_real_derivative
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state)
      space
      (identityCoframeMatterPrincipal derivativeDirection
        (matterCoordinateEquiv.symm direction))
      derivativeDirection

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_momentumDivergence_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence source
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        direction 0 =
      ∑ derivativeDirection : LorentzianIndex,
        (actionGeneratedConjugateMatterLocalJet
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
            source trajectoryTime state)
          space derivativeDirection
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_momentumDerivative_origin
      source trajectoryTime state space identityCoframe direction
        derivativeDirection

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_volume_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1) :
    generatedVolumeDensity
        (toContinuumPointField
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
            source trajectoryTime state space)
        0) =
      1 := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual,
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    identityCoframe]
  simp

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_algebraicCoefficient_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        direction 0 =
      ((sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state).conjugateMatter space
        (actionGeneratedMatterAlgebraicOperator
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
            source trajectoryTime state)
          space (matterCoordinateEquiv.symm direction))).re := by
  unfold matterAlgebraicDirectionalCoefficient
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_volume_origin
      source trajectoryTime state space identityCoframe,
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_algebraicVector_origin
      source trajectoryTime state space identityCoframe direction]
  rw [show
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
      source trajectoryTime state space).conjugateMatter 0 =
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state).conjugateMatter space by
    simpa only [
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual,
      sourceActionGeneratedLinearPlebanskiJointLocalActualLift,
      sourceActionGeneratedJointLocalActualLift,
      sourceActionGeneratedMatterDualScalarLocalActualLift] using
      sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin
        source
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state)
        space]
  simp

theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_matterEulerLagrange_origin
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe :
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state).coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient source
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
          source trajectoryTime state space)
        direction 0 =
      0 := by
  unfold matterEulerLagrangeDirectionalCoefficient
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_algebraicCoefficient_origin
      source trajectoryTime state space identityCoframe direction,
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_momentumDivergence_origin
      source trajectoryTime state space identityCoframe direction]
  have balance :=
    actionGeneratedConjugateMatterLocalJet_actionBalance
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state)
      space (matterCoordinateEquiv.symm direction)
  have realBalance := congrArg Complex.re balance
  simp only [Complex.re_sum] at realBalance
  exact sub_eq_zero.mpr realBalance.symm

/-! ## Exact P506/L0 current local action system -/

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_smooth
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
      trajectoryTime space).Smooth := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_smooth
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_nondegenerate
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
      trajectoryTime space).Nondegenerate := by
  apply
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_nondegenerate
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_coframe,
    positiveP506MatterCurrentLinearPlebanskiCauchyState_coframe_allSpace]
  simp

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_simplicity
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    GravitySimplicityEquation
      (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space) := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_simplicity
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_multiplier_nonzero
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
      trajectoryTime space).gravitySimplicityMultiplier point ≠
        0 := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual,
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual,
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_multiplier]
  exact
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_multiplier_nonzero
      trajectoryTime space

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_auxiliaryBalance
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    let actual :=
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space
    holonomicGravityCurvature actual 0 -
          gravityInternalDualEquiv (actual.gravityAuxiliary 0) +
          actual.gravitySimplicityMultiplier 0 =
        0 := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_auxiliaryBalance
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_p286AuxiliaryEquation
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    let actual :=
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space
    holonomicGaugeCurvature actual 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (actual.coframe 0))
        (actual.gaugeAuxiliary 0) := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_p286AuxiliaryEquation
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_gravityBianchi
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    let actual :=
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space
    covariantMixedCurvatureDerivative actual point first second third +
        covariantMixedCurvatureDerivative actual point second third first +
        covariantMixedCurvatureDerivative actual point third first second =
      0 := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_gravityBianchi
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space point
      first second third

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_p286Bianchi
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    let actual :=
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space
    covariantCurvatureDerivative actual point first second third +
        covariantCurvatureDerivative actual point second third first +
        covariantCurvatureDerivative actual point third first second =
      0 := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_p286Bianchi
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space point
      first second third

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_diracYukawa_origin
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
      (toContinuumPointField
        (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space)
        0) =
      0 := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_diracYukawa_origin
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space
      (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_coframe
        trajectoryTime space)

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_matterEulerLagrange_origin
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space)
        direction 0 =
      0 := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual_matterEulerLagrange_origin
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState space
      (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_coframe
        trajectoryTime space)
      direction

structure
    PositiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActionSystemLaw :
    Prop where
  upstreamCurrentActualGenerated :
    PositiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestartLaw
  currentSmooth :
    ∀ trajectoryTime space,
      (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space).Smooth
  currentNondegenerate :
    ∀ trajectoryTime space,
      (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space).Nondegenerate
  currentSimplicity :
    ∀ trajectoryTime space,
      GravitySimplicityEquation
        (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space)
  currentMultiplierNonzero :
    ∀ trajectoryTime space point,
      (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        trajectoryTime space).gravitySimplicityMultiplier point ≠
          0
  currentGravityAuxiliaryBalance :
    ∀ trajectoryTime space,
      let actual :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space
      holonomicGravityCurvature actual 0 -
            gravityInternalDualEquiv (actual.gravityAuxiliary 0) +
            actual.gravitySimplicityMultiplier 0 =
          0
  currentP286AuxiliaryEquation :
    ∀ trajectoryTime space,
      let actual :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space
      holonomicGaugeCurvature actual 0 =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear (actual.coframe 0))
          (actual.gaugeAuxiliary 0)
  currentGravityBianchi :
    ∀ trajectoryTime space point first second third,
      let actual :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space
      covariantMixedCurvatureDerivative actual point first second third +
          covariantMixedCurvatureDerivative actual point second third first +
          covariantMixedCurvatureDerivative actual point third first second =
        0
  currentP286Bianchi :
    ∀ trajectoryTime space point first second third,
      let actual :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space
      covariantCurvatureDerivative actual point first second third +
          covariantCurvatureDerivative actual point second third first +
          covariantCurvatureDerivative actual point third first second =
        0
  currentDiracYukawa :
    ∀ trajectoryTime space,
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
            trajectoryTime space)
          0) =
        0
  currentAdjointMatter :
    ∀ trajectoryTime space direction,
      matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
            trajectoryTime space)
          direction 0 =
        0
  currentInteractionSensitiveCurvature :
    ∀ trajectoryTime space,
      holonomicGravityCurvature
          (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
            trajectoryTime space)
          0 ≠
        gravityInternalDualEquiv
          (physicalIIPlusBivector (1 : LorentzianCoframe))

/-- Frontier theorem: the exact P506/L0 current-state producer supplies one
smooth, nondegenerate, interaction-sensitive local actual satisfying every
displayed gravity/P286/matter equation and both off-shell Bianchi identities.
No premise is accepted. -/
theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActionSystem_realizes :
    PositiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActionSystemLaw := by
  exact
    { upstreamCurrentActualGenerated :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestart_realizes
      currentSmooth :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_smooth
      currentNondegenerate :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_nondegenerate
      currentSimplicity :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_simplicity
      currentMultiplierNonzero :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_multiplier_nonzero
      currentGravityAuxiliaryBalance :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_auxiliaryBalance
      currentP286AuxiliaryEquation :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_p286AuxiliaryEquation
      currentGravityBianchi :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_gravityBianchi
      currentP286Bianchi :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_p286Bianchi
      currentDiracYukawa :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_diracYukawa_origin
      currentAdjointMatter :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_matterEulerLagrange_origin
      currentInteractionSensitiveCurvature :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_interactionSensitive }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiTrajectoryLocalActionSystem
