import H0mework.Physics.GaugeAction.P286Bianchi
import H0mework.Physics.MatterCurrent.FullSynchronizedResponseLocalActualLift

/-!
# C3h180 affine P286 background has zero curvature first jet

The original action-generated P286 local actual uses an affine primitive
connection.  This module records the background fact needed by the positive
second-jet producer: if its selected Cauchy connection value is zero, then its
actual ordered curvature first jet at the local origin is zero.  The result is
then transported along the definitional connection-preserving U7/UStar path.

This is only a background lemma for the forward V+Q producer.  It does not
construct a response, invert a residual, or assert a full-neighborhood shell.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286AffineCurvatureFirstJetBoundary

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286Bianchi
open StageNineP286BracketCalculus
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Generic affine-background calculation -/

/-- The affine connection has the same generated first derivative at every
base point, not only at the origin used by the public realization theorem. -/
theorem sourceGeneratedP286ActionLocalConnectionCoordinate_derivative_at
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          sourceGeneratedP286ActionLocalConnectionCoordinate source state
            space candidate formDirection)
        point derivativeDirection =
      sourceGeneratedP286ActionLocalConnectionJet source state space
        derivativeDirection formDirection := by
  unfold fieldDirectionalDerivative
    sourceGeneratedP286ActionLocalConnectionCoordinate
  rw [fderiv_const_add]
  rw [(sourceGeneratedP286ActionLocalIncrement source state space
    formDirection).hasFDerivAt.fderiv]
  fin_cases derivativeDirection <;>
    simp [sourceGeneratedP286ActionLocalIncrement, coordinateDirection,
      Fin.sum_univ_four]

/-- Bianchi's actual connection derivative is point-independent on the
source/action affine lift. -/
theorem sourceGeneratedP286ActionLocalActualLift_connectionDerivative_at
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    connectionCoordinateDerivative
        (sourceGeneratedP286ActionLocalActualLift source state space)
        point derivativeDirection formDirection =
      sourceGeneratedP286ActionLocalConnectionJet source state space
        derivativeDirection formDirection := by
  unfold connectionCoordinateDerivative connectionCoordinate
    sourceGeneratedP286ActionLocalActualLift
    sourceGeneratedP286ActionLocalConnection
  simp only [p286CoordinateEquiv.apply_symm_apply]
  exact sourceGeneratedP286ActionLocalConnectionCoordinate_derivative_at
    source state space point derivativeDirection formDirection

/-- Hence the second directional derivative of every primitive connection
coordinate vanishes. -/
theorem sourceGeneratedP286ActionLocalActualLift_connectionSecondDerivative_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (firstDerivative secondDerivative formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          connectionCoordinateDerivative
            (sourceGeneratedP286ActionLocalActualLift source state space)
            candidate firstDerivative formDirection)
        point secondDerivative = 0 := by
  have functionEquality :
      (fun candidate =>
        connectionCoordinateDerivative
          (sourceGeneratedP286ActionLocalActualLift source state space)
          candidate firstDerivative formDirection) =
        fun _ =>
          sourceGeneratedP286ActionLocalConnectionJet source state space
            firstDerivative formDirection := by
    funext candidate
    exact sourceGeneratedP286ActionLocalActualLift_connectionDerivative_at
      source state space candidate firstDerivative formDirection
  rw [functionEquality]
  simp [fieldDirectionalDerivative]

private theorem coordinateBracket_zero_right_local
    (first : P286CoordinateCarrier) :
    coordinateBracket first 0 = 0 := by
  have duplicated := coordinateBracket_add_right (0 : P286CoordinateCarrier) 0 first
  simp only [zero_add] at duplicated
  have cancelled :
      coordinateBracket first 0 + 0 =
        coordinateBracket first 0 + coordinateBracket first 0 := by
    simpa only [add_zero] using duplicated
  exact (add_left_cancel cancelled).symm

private theorem coordinateBracket_zero_left_local
    (second : P286CoordinateCarrier) :
    coordinateBracket 0 second = 0 := by
  have duplicated := coordinateBracket_add_left (0 : P286CoordinateCarrier) 0 second
  simp only [zero_add] at duplicated
  have cancelled :
      coordinateBracket 0 second + 0 =
        coordinateBracket 0 second + coordinateBracket 0 second := by
    simpa only [add_zero] using duplicated
  exact (add_left_cancel cancelled).symm

/-- If the selected Cauchy connection value vanishes, both bracket-Leibniz
terms in the curvature derivative vanish at the origin.  Together with the
zero affine second derivative this kills the complete ordered curvature first
jet. -/
theorem sourceGeneratedP286ActionLocalActualLift_orderedCurvatureFirstJet_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (connectionZero : ∀ direction,
      state.gaugeConnection space direction = 0)
    (derivativeDirection first second : LorentzianIndex) :
    orderedCurvatureDirectionalDerivative
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 derivativeDirection first second = 0 := by
  rw [orderedCurvatureDirectionalDerivative_eq_expansion
    (sourceGeneratedP286ActionLocalActualLift source state space)
    (sourceGeneratedP286ActionLocalActualLift_smooth source state space)]
  unfold orderedCurvatureDerivativeExpansion
  rw [sourceGeneratedP286ActionLocalActualLift_connectionSecondDerivative_zero,
    sourceGeneratedP286ActionLocalActualLift_connectionSecondDerivative_zero]
  have originZero (direction : LorentzianIndex) :
      connectionCoordinate
          (sourceGeneratedP286ActionLocalActualLift source state space)
          0 direction = 0 := by
    unfold connectionCoordinate sourceGeneratedP286ActionLocalActualLift
      sourceGeneratedP286ActionLocalConnection
    simp [sourceGeneratedP286ActionLocalConnectionCoordinate,
      sourceGeneratedP286ActionLocalIncrement, connectionZero]
  simp [originZero, coordinateBracket_zero_left_local,
    coordinateBracket_zero_right_local]

/-- Canonical six-pair form of the same actual zero first jet. -/
theorem sourceGeneratedP286ActionLocalActualLift_curvatureFirstJet_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (connectionZero : ∀ direction,
      state.gaugeConnection space direction = 0)
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            (sourceGeneratedP286ActionLocalActualLift source state space)
            point pair)
        0 derivativeDirection = 0 := by
  have functionEquality :
      (fun point =>
        holonomicP286GaugeCurvatureCoordinate
          (sourceGeneratedP286ActionLocalActualLift source state space)
          point pair) =
        fun point =>
          orderedCurvature
            (sourceGeneratedP286ActionLocalActualLift source state space)
            point (pairFirst pair) (pairSecond pair) := by
    funext point
    exact (orderedCurvature_canonicalPair_eq_holonomic
      (sourceGeneratedP286ActionLocalActualLift source state space)
      point pair).symm
  rw [functionEquality]
  exact sourceGeneratedP286ActionLocalActualLift_orderedCurvatureFirstJet_zero
    source state space connectionZero derivativeDirection
    (pairFirst pair) (pairSecond pair)

/-! ## Exact current-source specialization -/

private abbrev UAffine : StageNineHolonomicConfiguration :=
  sourceGeneratedP286ActionLocalActualLift
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentP286GaussCauchyState
    positiveP506MatterCurrentP286AxisContact

private abbrev U7 : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift

private abbrev UStar : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift

theorem positiveP506MatterCurrentP286GaussCauchyState_connection_axis_zero
    (direction : LorentzianIndex) :
    positiveP506MatterCurrentP286GaussCauchyState.gaugeConnection
        positiveP506MatterCurrentP286AxisContact direction = 0 := by
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gaugeConnection
        (canonicalCauchySlicePoint 0
          positiveP506MatterCurrentP286AxisContact) direction = 0
  rw [positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeConnection,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
  simp

theorem positiveP506MatterCurrentUAffine_curvatureFirstJet_zero
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point => holonomicP286GaugeCurvatureCoordinate UAffine point pair)
        0 derivativeDirection = 0 := by
  exact sourceGeneratedP286ActionLocalActualLift_curvatureFirstJet_zero
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentP286GaussCauchyState
    positiveP506MatterCurrentP286AxisContact
    positiveP506MatterCurrentP286GaussCauchyState_connection_axis_zero
    derivativeDirection pair

theorem positiveP506MatterCurrentU7_curvatureFirstJet_zero
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point => holonomicP286GaugeCurvatureCoordinate U7 point pair)
        0 derivativeDirection = 0 := by
  have functionEquality :
      (fun point => holonomicP286GaugeCurvatureCoordinate U7 point pair) =
        fun point => holonomicP286GaugeCurvatureCoordinate UAffine point pair := by
    funext point
    unfold holonomicP286GaugeCurvatureCoordinate holonomicGaugeCurvature
      p286ConnectionDerivative
    rw [positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeConnection]
  rw [functionEquality]
  exact positiveP506MatterCurrentUAffine_curvatureFirstJet_zero
    derivativeDirection pair

private theorem uStar_gaugeConnection_eq_U7 :
    UStar.gaugeConnection = U7.gaugeConnection := by
  calc
    UStar.gaugeConnection =
        positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeConnection :=
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeConnection
    _ = positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection :=
      positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeConnection
    _ = positiveP506MatterCurrentCompleteBaseActual.gaugeConnection :=
      positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeConnection
    _ = U7.gaugeConnection :=
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeConnection

/-- Exact background statement consumed by the complete V+Q second-jet
producer: UStar's existing affine connection contributes no curvature first
jet at the common origin. -/
theorem positiveP506MatterCurrentUStar_curvatureFirstJet_zero
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point => holonomicP286GaugeCurvatureCoordinate UStar point pair)
        0 derivativeDirection = 0 := by
  have functionEquality :
      (fun point => holonomicP286GaugeCurvatureCoordinate UStar point pair) =
        fun point => holonomicP286GaugeCurvatureCoordinate U7 point pair := by
    funext point
    unfold holonomicP286GaugeCurvatureCoordinate holonomicGaugeCurvature
      p286ConnectionDerivative
    rw [uStar_gaugeConnection_eq_U7]
  rw [functionEquality]
  exact positiveP506MatterCurrentU7_curvatureFirstJet_zero
    derivativeDirection pair

end

end SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286AffineCurvatureFirstJetBoundary
