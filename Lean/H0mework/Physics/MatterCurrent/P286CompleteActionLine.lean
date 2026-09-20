import H0mework.Physics.MatterCurrent.P286CompleteActionPrincipalFullSynchronizedActualLift
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.MatterCurrent.P286NonzeroCurvatureScalarLocalStationarity

/-!
# C3h181a: complete current action line

This module derives the current P286 Gauss charge and spatial auxiliary
velocity from the actual complete connection action on the generated U7
configuration.  The exact P506/L0 action graph forces the new charge to equal
the prior Gauss charge and forces the velocity into the third spatial channel
with value `-Q`.

These are action-owned forward readouts.  No residual inverse, supplied
endpoint, source knob, ansatz coefficient, branch choice, Boolean atomicity,
or stationarity certificate enters the construction.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBiradialCoframeResponse
open StageNineBiradialScalarOriginResponse
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineConnectionSectorSourceBalance
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaussRadialSecondJetLift
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineP286TemporalVelocitySecondJetLift
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCoframeStress
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286AffineCurvatureFirstJetBoundary
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def p286SpatialThirdOnly (component : P286CoordinateCarrier) :
    P286SpatialGaugeDirection :=
  fun axis => if axis = 2 then component else 0

def p286ThirdGaugeOneForm (component : P286CoordinateCarrier) :
    P286GaugeOneForm :=
  fun direction => if direction = 3 then component else 0

theorem canonicalSpatialThirdOnly_eq_thirdGaugeOneForm
    (component : P286CoordinateCarrier) :
    canonicalP286SpatialGaugeOneForm (p286SpatialThirdOnly component) =
      p286ThirdGaugeOneForm component := by
  funext direction
  refine Fin.cases ?_ (fun index => ?_) direction
  · exact canonicalP286SpatialGaugeOneForm_time
      (p286SpatialThirdOnly component)
  · rw [canonicalP286SpatialGaugeOneForm_spatial]
    fin_cases index <;>
      simp [p286SpatialThirdOnly, p286ThirdGaugeOneForm]

theorem diracGammaThree_eq_gammaZero_on_spinTwo
    (matter : SU7ExteriorSpinorMatterCarrier) :
    diracMatrixMatterAction diracGammaThree
        (fun spin => if spin = 2 then matter else 0) =
      diracMatrixMatterAction diracGammaZero
        (fun spin => if spin = 2 then matter else 0) := by
  funext spin
  fin_cases spin <;>
    simp [diracMatrixMatterAction, diracGammaZero, diracGammaThree,
      Fin.sum_univ_four]

theorem diracExteriorMotherLieAction_spinTwo_normalForm
    (matrix : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction matrix diracSpinTwoMatterProbe =
      fun spin =>
        if spin = 2 then
          exteriorSpinorMotherLieAction matrix p286HyperchargeMatterProbe
        else 0 := by
  funext spin
  fin_cases spin <;>
    simp [diracExteriorMotherLieAction, internalMatterLinearAction,
      diracSpinTwoMatterProbe]

def p286SpinTwoInternalVariation
    (component : P286CoordinateCarrier) : DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm component))
    diracSpinTwoMatterProbe

theorem temporalMatterVariation_normalForm
    (component : P286CoordinateCarrier) :
    holonomicMatterGaugeConnectionVariation
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (fun _ => p286TemporalGaugeOneForm component) 0 =
      fun direction =>
        if direction = 0 then
          p286SpinTwoInternalVariation component
        else 0 := by
  have matterEq :
      positiveP506MatterCurrentGravityCoupledLocalActualLift.matter 0 =
        diracSpinTwoMatterProbe :=
    positiveP506MatterCurrentGravityCoupledLocalActualLift_matter_origin
  unfold holonomicMatterGaugeConnectionVariation
  rw [matterEq]
  funext direction
  fin_cases direction
  case «0» => rfl
  all_goals simp [p286GaugeConnectionMotherVariation,
    p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection]

theorem spatialThirdMatterVariation_normalForm
    (component : P286CoordinateCarrier) :
    holonomicMatterGaugeConnectionVariation
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (fun _ => p286ThirdGaugeOneForm component) 0 =
      fun direction =>
        if direction = 3 then p286SpinTwoInternalVariation component else 0 := by
  have matterEq :
      positiveP506MatterCurrentGravityCoupledLocalActualLift.matter 0 =
        diracSpinTwoMatterProbe :=
    positiveP506MatterCurrentGravityCoupledLocalActualLift_matter_origin
  unfold holonomicMatterGaugeConnectionVariation
  rw [matterEq]
  funext direction
  fin_cases direction
  case «3» => rfl
  all_goals simp [p286GaugeConnectionMotherVariation,
    p286ThirdGaugeOneForm]

theorem matterGaugeKineticSum_spatialThird_eq_temporal
    (component : P286CoordinateCarrier) :
    StageNineP286GaugeConnectionActionVariation.matterGaugeKineticSum
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterCurrentGravityCoupledLocalActualLift 0)
        (holonomicMatterGaugeConnectionVariation
          positiveP506MatterCurrentGravityCoupledLocalActualLift
          (fun _ => p286ThirdGaugeOneForm component) 0) =
      StageNineP286GaugeConnectionActionVariation.matterGaugeKineticSum
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterCurrentGravityCoupledLocalActualLift 0)
        (holonomicMatterGaugeConnectionVariation
          positiveP506MatterCurrentGravityCoupledLocalActualLift
          (fun _ => p286TemporalGaugeOneForm component) 0) := by
  rw [spatialThirdMatterVariation_normalForm,
    temporalMatterVariation_normalForm]
  have coframeEq :
      (toContinuumPointField
        positiveP506MatterCurrentGravityCoupledLocalActualLift 0).coframe = 1 := by
    exact positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one 0
  unfold StageNineP286GaugeConnectionActionVariation.matterGaugeKineticSum
  rw [coframeEq]
  simp only [Fin.sum_univ_four]
  simp [matterDerivativeFrameRelative, matterFrameRelative]
  change
    diracMatrixMatterAction
        (inverseCoframeDiracGamma identityCoframeMatterGeometry 3)
        (p286SpinTwoInternalVariation component) =
      diracMatrixMatterAction
        (inverseCoframeDiracGamma identityCoframeMatterGeometry 0)
        (p286SpinTwoInternalVariation component)
  rw [inverseCoframeDiracGamma_identity,
    inverseCoframeDiracGamma_identity]
  change
    diracMatrixMatterAction diracGammaThree
        (p286SpinTwoInternalVariation component) =
      diracMatrixMatterAction diracGammaZero
        (p286SpinTwoInternalVariation component)
  unfold p286SpinTwoInternalVariation
  rw [diracExteriorMotherLieAction_spinTwo_normalForm]
  exact diracGammaThree_eq_gammaZero_on_spinTwo _

theorem p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
    (configuration : StageNineHolonomicConfiguration)
    (connectionZero : configuration.gaugeConnection 0 = 0)
    (direction : P286GaugeOneForm) :
    p286GaugeBFAlgebraicCoefficient configuration direction 0 = 0 := by
  have algebraicZero :
      p286GaugeConnectionAlgebraicCurvatureDirection configuration direction
          0 =
        0 := by
    funext pair
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
      holonomicP286GaugeConnectionCoordinate
    simp only [connectionZero, Pi.zero_apply, map_zero,
      p286CoordinateLieBracket_zero_left,
      p286CoordinateLieBracket_zero_right, zero_add]
  unfold p286GaugeBFAlgebraicCoefficient
  rw [algebraicZero]
  simp

theorem p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
    (configuration : StageNineHolonomicConfiguration)
    (derivativeZero :
      ∀ formDirection,
        holonomicScalarCovariantDerivative configuration 0 formDirection = 0)
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource configuration
        direction 0 =
      0 := by
  unfold p286ScalarCurrentCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
  have pointDerivativeZero :
      (toContinuumPointField configuration 0).scalarCovariantDerivative = 0 := by
    funext formDirection
    exact derivativeZero formDirection
  rw [pointDerivativeZero]
  simp [scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe]

theorem p286MatterCurrentCoefficient_spatialThird_eq_temporal
    (component : P286CoordinateCarrier) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (p286ThirdGaugeOneForm component) 0 =
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (p286TemporalGaugeOneForm component) 0 := by
  unfold p286MatterCurrentCoefficient
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [matterGaugeKineticSum_spatialThird_eq_temporal]

theorem algebraicCurrent_spatialThird_eq_temporal
    (component : P286CoordinateCarrier) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (canonicalP286SpatialGaugeOneForm (p286SpatialThirdOnly component)) 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (p286TemporalGaugeOneForm component) 0 := by
  rw [canonicalSpatialThirdOnly_eq_thirdGaugeOneForm]
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors,
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  rw [p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl) (p286ThirdGaugeOneForm component),
    p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl) (p286TemporalGaugeOneForm component),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0) (p286ThirdGaugeOneForm component),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0) (p286TemporalGaugeOneForm component)]
  simpa using p286MatterCurrentCoefficient_spatialThird_eq_temporal component

theorem p286MatterCurrentCoefficient_origin_eq_of_contact
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe 0 = second.coframe 0)
    (matterEq : first.matter 0 = second.matter 0)
    (conjugateEq : first.conjugateMatter 0 = second.conjugateMatter 0)
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource first direction 0 =
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource second direction
        0 := by
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [coframeEq, matterEq, conjugateEq]

theorem currentU7_gaugeConnection_origin_zero :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection
        0 =
      0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  simpa [currentP506MatterP286ConnectionCoordinate] using
    currentP506MatterP286ConnectionCoordinate_origin_zero direction

theorem currentU7_coframe_origin_one :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe 0 =
      1 := by
  rw [positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_coframe_biradial]
  exact biradialCoframe_one_one

theorem actionGeneratedMatterLocalField_zeroSlice_of_constant
    (state : StageNineCauchyState) (anchor : StageNineSpatialPoint)
    (target : DiracExteriorMatterCarrier)
    (stateMatter : state.matter = fun _ => target)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterLocalField state anchor
        (canonicalCauchySlicePoint 0 space) = target := by
  have spatialDerivativeZero (direction : Fin 3) :
      cauchyMatterSpatialDerivativeCoordinate state anchor direction = 0 := by
    unfold cauchyMatterSpatialDerivativeCoordinate
    rw [stateMatter]
    simp
  apply matterCoordinateEquiv.injective
  simp [actionGeneratedMatterLocalField,
    actionGeneratedMatterLocalCoordinate,
    actionGeneratedMatterLocalIncrement,
    actionGeneratedMatterLocalJetCoordinate,
    stateMatter, spatialDerivativeZero,
    canonicalCauchySlicePoint, Fin.sum_univ_four]

theorem currentEinsteinCartanLocalActualLift_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentEinsteinCartanCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentEinsteinCartanCauchyState 0
    diracSpinTwoMatterProbe
    positiveP506MatterCurrentEinsteinCartanCauchyState_matter_constant
    space

theorem currentLinearPlebanskiLocalActualLift_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  have retained :
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.matter :=
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_realizes
      |>.retainsBasePrimitiveFields |>.2 |>.2 |>.2 |>.2 |>.2 |>.1
  have baseEq :
      positiveP506MatterCurrentLinearPlebanskiBaseActual.matter =
        positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter :=
    congrArg StageNineHolonomicConfiguration.matter
      positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual
  calc
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter
          (canonicalCauchySlicePoint 0 space) =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.matter
          (canonicalCauchySlicePoint 0 space) :=
      congrFun retained _
    _ = positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter
          (canonicalCauchySlicePoint 0 space) :=
      congrFun baseEq _
    _ = _ := currentEinsteinCartanLocalActualLift_matter_zeroSlice space

theorem currentLinearPlebanskiCauchyState_matter_allSpace :
    positiveP506MatterCurrentLinearPlebanskiCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold positiveP506MatterCurrentLinearPlebanskiCauchyState
    canonicalCauchyRestriction
  exact currentLinearPlebanskiLocalActualLift_matter_zeroSlice space

theorem currentU7_matter_origin :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.matter 0 =
      diracSpinTwoMatterProbe := by
  change
    (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
      positiveP506MatterCurrentP286GaussCauchyState
      positiveP506MatterCurrentP286AxisContact).matter 0 =
      _
  rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.matter
        (canonicalCauchySlicePoint 0
          positiveP506MatterCurrentP286AxisContact) =
      _
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentLinearPlebanskiCauchyState 0
        (canonicalCauchySlicePoint 0
          positiveP506MatterCurrentP286AxisContact) =
      _
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentLinearPlebanskiCauchyState 0
    diracSpinTwoMatterProbe currentLinearPlebanskiCauchyState_matter_allSpace
    positiveP506MatterCurrentP286AxisContact

theorem currentU7_actionCurrent_origin_eq_currentU5
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift direction
        0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift direction 0 := by
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors,
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  rw [p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      currentU7_gaugeConnection_origin_zero,
    p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_origin_zero,
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0)]
  simp only [zero_add]
  apply p286MatterCurrentCoefficient_origin_eq_of_contact
  · rw [currentU7_coframe_origin_one,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one]
  · rw [currentU7_matter_origin,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_matter_origin]
  · rw [
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugate_origin]

theorem currentMomentum_actionCurrent_origin_eq_currentU5
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift direction 0 := by
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors,
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  rw [p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift (by
        change
          positiveP506MatterCurrentGravityCoupledLocalActualLift.gaugeConnection
              0 =
            0
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift (by
        intro formDirection
        change
          holonomicScalarCovariantDerivative
              positiveP506MatterCurrentGravityCoupledLocalActualLift 0
              formDirection =
            0
        exact
          positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
            0 formDirection),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0)]
  simp only [zero_add]
  apply p286MatterCurrentCoefficient_origin_eq_of_contact <;> rfl

theorem currentGaussCharge_eq_priorGaussCharge :
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge =
      positiveP506MatterCurrentGravityCoupledP286GaussCharge := by
  apply p286CoordinateLiePairingDualOperator_injective
  apply LinearMap.ext
  intro component
  rw [p286CoordinateLiePairingDualOperator_apply,
    p286CoordinateLiePairingDualOperator_apply,
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response,
    positiveP506MatterCurrentGravityCoupledP286GaussCharge_response]
  calc
    positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
          component =
        p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          (p286TemporalGaugeOneForm component) 0 := rfl
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentGravityCoupledLocalActualLift
          (p286TemporalGaugeOneForm component) 0 :=
      currentU7_actionCurrent_origin_eq_currentU5 _
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
          (p286TemporalGaugeOneForm component) 0 :=
      (currentMomentum_actionCurrent_origin_eq_currentU5 _).symm
    _ = positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget
          component := rfl

def p286SpatialAxisOnly (axis : Fin 3)
    (component : P286CoordinateCarrier) : P286SpatialGaugeDirection :=
  fun current => if current = axis then component else 0

theorem spatialAxisMatterVariation_normalForm
    (axis : Fin 3) (component : P286CoordinateCarrier) :
    holonomicMatterGaugeConnectionVariation
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (fun _ => canonicalP286SpatialGaugeOneForm
          (p286SpatialAxisOnly axis component)) 0 =
      fun direction =>
        if direction = axis.succ then p286SpinTwoInternalVariation component
        else 0 := by
  have matterEq :
      positiveP506MatterCurrentGravityCoupledLocalActualLift.matter 0 =
        diracSpinTwoMatterProbe :=
    positiveP506MatterCurrentGravityCoupledLocalActualLift_matter_origin
  unfold holonomicMatterGaugeConnectionVariation
  rw [matterEq]
  funext direction
  refine Fin.cases ?_ (fun index => ?_) direction
  · have timeNe : (0 : LorentzianIndex) ≠ axis.succ :=
      (Fin.succ_ne_zero axis).symm
    simp [p286GaugeConnectionMotherVariation,
      canonicalP286SpatialGaugeOneForm, timeNe]
  · unfold p286GaugeConnectionMotherVariation
    change
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (canonicalP286SpatialGaugeOneForm
                (p286SpatialAxisOnly axis component) index.succ)))
          diracSpinTwoMatterProbe =
        _
    rw [canonicalP286SpatialGaugeOneForm_spatial]
    by_cases sameAxis : index = axis
    · subst index
      simp [p286SpatialAxisOnly,
        p286SpinTwoInternalVariation]
    · simp [p286SpatialAxisOnly, sameAxis]

theorem diracSpinZeroMatterCoordinate_gammaOne_on_spinTwo_zero
    (matter : SU7ExteriorSpinorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (diracMatrixMatterAction diracGammaOne
          (fun spin => if spin = 2 then matter else 0)) =
      0 := by
  simp [diracSpinZeroMatterCoordinate, diracMatrixMatterAction,
    diracGammaOne, Fin.sum_univ_four]

theorem diracSpinZeroMatterCoordinate_gammaTwo_on_spinTwo_zero
    (matter : SU7ExteriorSpinorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (diracMatrixMatterAction diracGammaTwo
          (fun spin => if spin = 2 then matter else 0)) =
      0 := by
  simp [diracSpinZeroMatterCoordinate, diracMatrixMatterAction,
    diracGammaTwo, Fin.sum_univ_four]

theorem p286MatterCurrentCoefficient_spatialAxis_zero_of_ne_third
    (axis : Fin 3) (axisNotThird : axis ≠ 2)
    (component : P286CoordinateCarrier) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (canonicalP286SpatialGaugeOneForm
          (p286SpatialAxisOnly axis component)) 0 =
      0 := by
  unfold p286MatterCurrentCoefficient
  rw [spatialAxisMatterVariation_normalForm]
  have coframeEq :
      (toContinuumPointField
        positiveP506MatterCurrentGravityCoupledLocalActualLift 0).coframe = 1 := by
    exact positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one 0
  have conjugateEq :
      (toContinuumPointField
        positiveP506MatterCurrentGravityCoupledLocalActualLift 0).conjugateMatter =
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
    exact positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugate_origin
  unfold generatedVolumeDensity
  rw [coframeEq]
  simp only [Matrix.det_one, abs_one, one_mul]
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [conjugateEq, coframeEq]
  rw [show
    ({ coframe := 1, derivative := 0 } : PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  fin_cases axis
  all_goals simp at axisNotThird
  all_goals simp [matterDualFrameRelative, matterDerivativeFrameRelative,
    matterFrameRelative, p286SpinTwoInternalVariation,
    diracExteriorMotherLieAction_spinTwo_normalForm, diracGamma,
    diracSpinZeroMatterCoordinate_gammaOne_on_spinTwo_zero,
    diracSpinZeroMatterCoordinate_gammaTwo_on_spinTwo_zero,
    Fin.sum_univ_four]

theorem algebraicCurrent_spatialAxis_zero_of_ne_third
    (axis : Fin 3) (axisNotThird : axis ≠ 2)
    (component : P286CoordinateCarrier) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (canonicalP286SpatialGaugeOneForm
          (p286SpatialAxisOnly axis component)) 0 =
      0 := by
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  rw [p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0),
    p286MatterCurrentCoefficient_spatialAxis_zero_of_ne_third axis
      axisNotThird component]
  simp

theorem canonicalSpatialDirection_eq_axisSum
    (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm direction =
      canonicalP286SpatialGaugeOneForm
          (p286SpatialAxisOnly 0 (direction 0)) +
        canonicalP286SpatialGaugeOneForm
          (p286SpatialAxisOnly 1 (direction 1)) +
        canonicalP286SpatialGaugeOneForm
          (p286SpatialAxisOnly 2 (direction 2)) := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.add_apply]
    fin_cases index <;> simp [p286SpatialAxisOnly]

theorem algebraicCurrent_spatial_eq_temporalThird
    (direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift
        (p286TemporalGaugeOneForm (direction 2)) 0 := by
  rw [canonicalSpatialDirection_eq_axisSum]
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_add_action,
    p286GaugeConnectionAlgebraicCurrentCoefficient_add_action]
  rw [algebraicCurrent_spatialAxis_zero_of_ne_third 0 (by decide),
    algebraicCurrent_spatialAxis_zero_of_ne_third 1 (by decide)]
  simp only [zero_add]
  have axisThirdEq :
      p286SpatialAxisOnly 2 (direction 2) =
        p286SpatialThirdOnly (direction 2) := by
    funext axis
    fin_cases axis <;>
      simp [p286SpatialAxisOnly, p286SpatialThirdOnly]
  rw [axisThirdEq]
  exact algebraicCurrent_spatialThird_eq_temporal (direction 2)

theorem currentSpatialActionTarget_eq_temporalThird
    (direction : P286SpatialGaugeDirection) :
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget
        direction =
      positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
        (direction 2) := by
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        (canonicalP286SpatialGaugeOneForm direction) 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        (p286TemporalGaugeOneForm (direction 2)) 0
  rw [currentU7_actionCurrent_origin_eq_currentU5,
    currentU7_actionCurrent_origin_eq_currentU5]
  exact algebraicCurrent_spatial_eq_temporalThird direction

theorem thirdNegCharge_legendreResponse :
    p286SpatialBFLegendreDualOperator
        (p286SpatialThirdOnly
          (-positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)) =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget := by
  apply LinearMap.ext
  intro direction
  rw [p286SpatialBFLegendreDualOperator_apply,
    Fin.sum_univ_three]
  simp only [p286SpatialThirdOnly]
  simp only [if_neg (by decide : (0 : Fin 3) ≠ 2),
    if_neg (by decide : (1 : Fin 3) ≠ 2), if_pos,
    p286CoordinateLiePairing_zero_left, zero_add]
  rw [show
      -positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge =
        (-1 : ℝ) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge by simp,
    p286CoordinateLiePairing_smul_left,
    currentSpatialActionTarget_eq_temporalThird,
    ← positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response]
  ring

theorem currentSpatialAuxiliaryVelocity_eq_thirdNegCharge :
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity =
      p286SpatialThirdOnly
        (-positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) := by
  exact
    (positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_unique
      _ thirdNegCharge_legendreResponse).symm


end

end SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
