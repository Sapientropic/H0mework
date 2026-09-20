import H0mework.Physics.Geometry.BiradialScalarOriginResponse
import H0mework.Physics.MatterCurrent.P286NonzeroCurvatureSynchronizedLocalActualLift

/-!
# S9-C3h164: scalar stationarity on the current-generated nonzero P286 actual

C3h163 has already generated the synchronized local actual `U₇` from the
actual P506 matter current, the unique Gauss response, and the P286 action.
This module does not alter that actual and does not transport the scalar
stationarity theorem proved earlier for the zero-connection `U₆`.

Instead it computes the new affine P286 connection coordinate and first jet.
At the canonical origin the connection vanishes, while every diagonal first
derivative vanishes.  Together with the retained source-vacuum scalar and the
biradial coframe law, these facts close the scalar differential divergence;
the kinetic, potential, and Yukawa algebraic terms are then recomputed on the
same `U₇`.  The module also reads the P286 auxiliary origin equation directly
from the action-generated curvature law.

No source slot, residual inverse, endpoint witness, branch receipt, or supplied
stationarity certificate is introduced.  The remaining P286 connection,
coframe, and gravity equations on `U₇` stay outside this checkpoint.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBiradialCoframeResponse
open StageNineBiradialScalarOriginResponse
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarVariation
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCartanActual
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
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

theorem currentU6_scalar_vacuum :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change positiveP506MatterCurrentGravityCoupledLocalActualLift.scalar = _
  exact positiveP506MatterCurrentGravityCoupledLocalActualLift_scalar_vacuum

theorem currentBaseActual_scalar_vacuum :
    positiveP506MatterCurrentGravityCoupledBaseActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  exact
    positiveP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift_scalar_vacuum

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    actionGeneratedScalarLocalField
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact =
      _
  funext point
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    positiveP506MatterCurrentP286GaussCauchyState,
    canonicalCauchyRestriction, currentU6_scalar_vacuum,
    currentBaseActual_scalar_vacuum,
    fieldDirectionalDerivative, Fin.sum_univ_four]

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_coframe_biradial :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe =
      fun _ => biradialCoframe 1 1 := by
  funext point
  change
    positiveP506MatterCurrentP286GaussCauchyState.coframe
        positiveP506MatterCurrentP286AxisContact =
      biradialCoframe 1 1
  rw [positiveP506MatterCurrentP286GaussCauchyState_coframe_axis,
    biradialCoframe_one_one]

def currentP506MatterP286ConnectionCoordinate
    (point : BasePoint) (direction : LorentzianIndex) :
    P286CoordinateCarrier :=
  p286CoordinateEquiv
    (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection
      point direction)

theorem currentP506MatterP286ConnectionCoordinate_eq_generated
    (point : BasePoint) (direction : LorentzianIndex) :
    currentP506MatterP286ConnectionCoordinate point direction =
      sourceGeneratedP286ActionLocalConnectionCoordinate
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact point direction := by
  unfold currentP506MatterP286ConnectionCoordinate
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeConnection]
  exact p286CoordinateEquiv.apply_symm_apply _

theorem currentP506MatterP286ConnectionCoordinate_origin_zero
    (direction : LorentzianIndex) :
    currentP506MatterP286ConnectionCoordinate 0 direction = 0 := by
  rw [currentP506MatterP286ConnectionCoordinate_eq_generated]
  unfold sourceGeneratedP286ActionLocalConnectionCoordinate
    sourceGeneratedP286ActionLocalIncrement
  simp only [map_zero, add_zero]
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    p286CoordinateEquiv
        (positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gaugeConnection
          (canonicalCauchySlicePoint 0
            positiveP506MatterCurrentP286AxisContact) direction) =
      0
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeConnection]
  rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
  simp

theorem currentP506MatterP286ConnectionCoordinate_directionalDerivative
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          currentP506MatterP286ConnectionCoordinate point formDirection)
        0 derivativeDirection =
      sourceGeneratedP286ActionLocalConnectionJet
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact
        derivativeDirection formDirection := by
  rw [show
    (fun point =>
      currentP506MatterP286ConnectionCoordinate point formDirection) =
      fun point =>
        sourceGeneratedP286ActionLocalConnectionCoordinate
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286GaussCauchyState
          positiveP506MatterCurrentP286AxisContact point formDirection by
      funext point
      exact currentP506MatterP286ConnectionCoordinate_eq_generated point _]
  exact sourceGeneratedP286ActionLocalConnection_derivative_eq_jet
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentP286GaussCauchyState
    positiveP506MatterCurrentP286AxisContact
    derivativeDirection formDirection

theorem currentP506MatterP286ConnectionCoordinate_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          currentP506MatterP286ConnectionCoordinate point direction)
        0 direction =
      0 := by
  rw [currentP506MatterP286ConnectionCoordinate_directionalDerivative]
  fin_cases direction <;>
    simp [sourceGeneratedP286ActionLocalConnectionJet]

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_eq_fixedVacuumAction
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        point direction =
      scalarP286ActionBilinear
        (currentP506MatterP286ConnectionCoordinate point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarCovariantDerivative
  rw [positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  unfold currentP506MatterP286ConnectionCoordinate
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection
            point direction))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection
                point direction))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rw [p286CoordinateEquiv.symm_apply_apply]

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_origin_zero
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        0 direction =
      0 := by
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_eq_fixedVacuumAction,
    currentP506MatterP286ConnectionCoordinate_origin_zero]
  simp

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_directionalDerivative
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative
            positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
            point formDirection)
        0 derivativeDirection =
      scalarP286ActionBilinear
        (sourceGeneratedP286ActionLocalConnectionJet
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286GaussCauchyState
          positiveP506MatterCurrentP286AxisContact
          derivativeDirection formDirection)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    currentP506MatterP286ConnectionCoordinate point formDirection
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    have smooth :=
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_smooth
        |>.2.2.2.2.1 formDirection
    simpa [connection, currentP506MatterP286ConnectionCoordinate] using
      (smooth.differentiable (by simp)).differentiableAt
  have actionDerivative :
      fderiv ℝ
          (fun point =>
            action (connection point)
              (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
          0 =
        (action.flip
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
            (fderiv ℝ connection 0) :=
    ((action.flip
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).hasFDerivAt.comp
      0 connectionDifferentiable.hasFDerivAt).fderiv
  rw [show (fun point =>
      holonomicScalarCovariantDerivative
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        point formDirection) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_eq_fixedVacuumAction
        point formDirection]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  change scalarP286ActionBilinear
      (fieldDirectionalDerivative connection 0 derivativeDirection)
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = _
  exact congrArg
    (fun coordinate => scalarP286ActionBilinear coordinate
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
    (currentP506MatterP286ConnectionCoordinate_directionalDerivative
      derivativeDirection formDirection)

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative
            positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
            point direction)
        0 direction =
      0 := by
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_directionalDerivative]
  have diagonalZero :
      sourceGeneratedP286ActionLocalConnectionJet
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286GaussCauchyState
          positiveP506MatterCurrentP286AxisContact direction direction =
        0 := by
    fin_cases direction <;>
      simp [sourceGeneratedP286ActionLocalConnectionJet]
  rw [diagonalZero]
  simp

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarDivergence_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction 0 =
      0 := by
  apply scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      (a := 1) (b := 1)
  · norm_num
  · norm_num
  · exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_coframe_biradial
  · intro formDirection
    exact
      ((holonomicScalarCovariantDerivative_contDiff
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_smooth
        formDirection).differentiable (by simp)).differentiableAt
  · exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_diagonalDerivative_zero

theorem currentEinsteinCartanCauchyState_conjugate_allSpace
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentEinsteinCartanCauchyState.conjugateMatter space =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (positiveP506MatterCurrentCartanTrajectoryState 0).conjugateMatter space =
      _
  rw [positiveP506MatterCurrentCartanTrajectoryState_zero]
  change
    (positiveSourceTargetMatterCauchyState).conjugateMatter space = _
  simpa [positiveSourceTargetMatterCauchyState,
    sourceTargetMatterCauchyState] using
      positiveSourceTargetMatterCauchyState_conjugate

theorem actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
    (state : StageNineCauchyState)
    (anchor : StageNineSpatialPoint)
    (target : Module.Dual ℂ DiracExteriorMatterCarrier)
    (stateConjugate : state.conjugateMatter = fun _ => target)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterLocalField state anchor
        (canonicalCauchySlicePoint 0 space) = target := by
  have spatialDerivativeZero (direction : Fin 3) :
      cauchyConjugateMatterSpatialDerivativeCoordinate state anchor direction =
        0 := by
    unfold cauchyConjugateMatterSpatialDerivativeCoordinate
    rw [stateConjugate]
    simp
  unfold actionGeneratedConjugateMatterLocalField
  rw [stateConjugate]
  simp [canonicalCauchySlicePoint,
    actionGeneratedConjugateMatterLocalJet,
    cauchyConjugateMatterSpatialDerivative,
    spatialDerivativeZero, Fin.sum_univ_four]

theorem
    sourceActionGeneratedCurrentEinsteinCartanFeedbackLocalActualLift_conjugate_zeroSlice_of_constant
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (contact space : StageNineSpatialPoint)
    (target : Module.Dual ℂ DiracExteriorMatterCarrier)
    (stateConjugate :
      (sourceActionGeneratedCurrentEinsteinCartanFeedbackCauchyState
        source anchor trajectoryTime state).conjugateMatter =
          fun _ => target) :
    (sourceActionGeneratedCurrentEinsteinCartanFeedbackLocalActualLift
      source anchor trajectoryTime state contact).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      target := by
  exact actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
    (sourceActionGeneratedCurrentEinsteinCartanFeedbackCauchyState
      source anchor trajectoryTime state)
    contact target stateConjugate space

theorem currentEinsteinCartanLocalActualLift_conjugate_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentEinsteinCartanLocalActualLift.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  have stateConjugate :
      positiveP506MatterCurrentEinsteinCartanCauchyState.conjugateMatter =
        fun _ =>
          (diracSpinZeroMatterCoordinate :
            Module.Dual ℂ DiracExteriorMatterCarrier) := by
    funext candidate
    exact currentEinsteinCartanCauchyState_conjugate_allSpace candidate
  exact
    sourceActionGeneratedCurrentEinsteinCartanFeedbackLocalActualLift_conjugate_zeroSlice_of_constant
      positiveSmoothUnifiedSource 0 0 positiveSourceTargetMatterCauchyState
      0 space diracSpinZeroMatterCoordinate stateConjugate

theorem currentLinearPlebanskiLocalActualLift_conjugate_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  have retained :
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.conjugateMatter =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.conjugateMatter :=
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_realizes
      |>.retainsBasePrimitiveFields |>.2 |>.2 |>.2 |>.2 |>.2 |>.2
  have baseEq :
      positiveP506MatterCurrentLinearPlebanskiBaseActual.conjugateMatter =
        positiveP506MatterCurrentEinsteinCartanLocalActualLift.conjugateMatter :=
    congrArg StageNineHolonomicConfiguration.conjugateMatter
      positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual
  calc
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.conjugateMatter
          (canonicalCauchySlicePoint 0 space) =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.conjugateMatter
          (canonicalCauchySlicePoint 0 space) :=
      congrFun retained _
    _ = positiveP506MatterCurrentEinsteinCartanLocalActualLift.conjugateMatter
          (canonicalCauchySlicePoint 0 space) :=
      congrFun baseEq _
    _ = _ := currentEinsteinCartanLocalActualLift_conjugate_zeroSlice space

theorem currentLinearPlebanskiCauchyState_conjugate_allSpace :
    positiveP506MatterCurrentLinearPlebanskiCauchyState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold positiveP506MatterCurrentLinearPlebanskiCauchyState
    canonicalCauchyRestriction
  exact currentLinearPlebanskiLocalActualLift_conjugate_zeroSlice space

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.conjugateMatter
        0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
      positiveP506MatterCurrentP286GaussCauchyState
      positiveP506MatterCurrentP286AxisContact).conjugateMatter 0 =
      _
  rw [sourceActionGeneratedJointLocalActualLift_initialConjugateMatter]
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.conjugateMatter
        (canonicalCauchySlicePoint 0
          positiveP506MatterCurrentP286AxisContact) =
      _
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_conjugateMatter,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugateMatter,
    positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentLinearPlebanskiCauchyState 0
        (canonicalCauchySlicePoint 0
          positiveP506MatterCurrentP286AxisContact) =
      _
  have stateConjugate :=
    currentLinearPlebanskiCauchyState_conjugate_allSpace
  have spatialDerivativeZero (direction : Fin 3) :
      cauchyConjugateMatterSpatialDerivativeCoordinate
          positiveP506MatterCurrentLinearPlebanskiCauchyState 0 direction =
        0 := by
    unfold cauchyConjugateMatterSpatialDerivativeCoordinate
    rw [stateConjugate]
    simp
  unfold actionGeneratedConjugateMatterLocalField
  rw [stateConjugate]
  simp [positiveP506MatterCurrentP286AxisContact,
    canonicalCauchySlicePoint, canonicalSpatialCoordinateDirection,
    actionGeneratedConjugateMatterLocalJet,
    cauchyConjugateMatterSpatialDerivative,
    spatialDerivativeZero, Fin.sum_univ_four]

/-! ## Scalar algebraic response on the nonzero-curvature actual -/

theorem
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarKineticAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0)
        (holonomicScalarVariationAlgebraicDirection
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          direction 0) =
      0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeOrigin :
      (toContinuumPointField
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        0).scalarCovariantDerivative =
        0 := by
    funext formDirection
    exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_origin_zero
        formDirection
  rw [covariantDerivativeOrigin]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarPotential_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0)
        direction =
      0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0).scalar =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    exact congrFun
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum
      0]
  simp

theorem
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarYukawa_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0)
        direction =
      0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  rw [show
    (toContinuumPointField
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      0).conjugateMatter = diracSpinZeroMatterCoordinate by
    exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  norm_num

theorem
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction 0 =
      0 := by
  unfold scalarAlgebraicDirectionalCoefficient
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarKineticAlgebraic_origin_zero,
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarPotential_origin_zero,
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarYukawa_origin_zero]
  ring

/-- The scalar Euler--Lagrange coefficient is recomputed on the new actual;
it is not transported from the zero-P286-connection `U₆`. -/
theorem
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarEuler_origin
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction 0 =
      0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarAlgebraic_origin_zero,
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarDivergence_origin_zero]
  ring

theorem
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_p286AuxiliaryEquation_origin :
    holonomicGaugeCurvature
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe
              0))
        (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
          0) := by
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeCurvature]
  rfl

/-! ## Downstream C3h164 recomputation bundle -/

/-- The C3h163 source/action-produced nonzero-curvature actual also satisfies
its P286 auxiliary equation and its fully recomputed scalar contact equation.
This proposition stores no source certificate and introduces no branch choice. -/
structure PositiveP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarityLaw :
    Prop where
  synchronizedActualGenerated :
    PositiveP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLaw
  p286AuxiliaryEquationOrigin :
    holonomicGaugeCurvature
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe
              0))
        (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
          0)
  scalarVacuum :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  scalarDivergenceOrigin :
    ∀ direction : ScalarCoordinateCarrier,
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          direction 0 =
        0
  scalarEulerOrigin :
    ∀ direction : ScalarCoordinateCarrier,
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          direction 0 =
        0

theorem
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_realizes_C3h164 :
    PositiveP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarityLaw := by
  exact
    { synchronizedActualGenerated :=
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_realizes_C3h163
      p286AuxiliaryEquationOrigin :=
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_p286AuxiliaryEquation_origin
      scalarVacuum :=
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum
      scalarDivergenceOrigin :=
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarDivergence_origin_zero
      scalarEulerOrigin :=
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarEuler_origin }

end

end SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
