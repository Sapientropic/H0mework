import H0mework.Physics.MatterCurrent.P286CompleteActionLine

/-!
# C3h181: full nonlinear P286 response and independent scalar constraint

The C3h180 action-principal second jet is evaluated on the complete current
action line generated in C3h181a.  The resulting synchronized actual has an
explicit connection normal form in one action-generated P286 charge direction.
Consequently the actual non-Abelian self-bracket vanishes by the Lie bracket
definition, and the full `dA + [A,A]` curvature agrees with the actual
coframe-Hodge auxiliary response at every local point.

That full-domain auxiliary equation is producer soundness: the same P286
action generated the charge, velocity, and second jet.  It is not counted as
an independent equation.  The scalar Euler--Lagrange coefficient is separately
recomputed at the common origin on the same final actual; no P286 constructor
solved that equation.

No residual inversion, endpoint witness, supplied equation certificate,
source tuning, ansatz coefficient, boundary constant, or branch receipt is
accepted.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift

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
open StageNineP286Bianchi
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
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
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


abbrev c3h181StrongCouplingSquared : ℝ :=
  ((sourceGeneratedUnifiedCouplings
    positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)

def c3h181U7ConnectionNormalForm (point : BasePoint) : P286GaugeOneForm :=
  fun direction =>
    if direction = 1 then
      (c3h181StrongCouplingSquared / 3 *
        point canonicalLorentzianTimeDirection) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
    else 0

theorem positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate_normalForm :
    positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate =
      ![0, 0, 0,
        (1 / 3 : ℝ) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0] := by
  rw [currentGaussCharge_eq_priorGaussCharge]
  funext pair
  unfold positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate
    positiveP506MatterCurrentP286GaussCauchyState
    positiveP506MatterCurrentP286AxisContact canonicalCauchyRestriction
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
  simp only [p286CoordinateEquiv.apply_symm_apply]
  unfold positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate
    p286GaussRadialAuxiliaryProfile p286GaussAuxiliaryAxisEmbedding
    p286SpatialAuxiliaryVelocityEmbedding
  fin_cases pair <;>
    simp [canonicalCauchySlicePoint, canonicalSpatialCoordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

theorem actionGeneratedP286ExteriorDerivativeCoordinate_normalForm :
    (fun pair =>
      actionGeneratedP286ExteriorDerivativeCoordinate
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact pair) =
      ![(c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0, 0, 0, 0] := by
  funext pair
  unfold actionGeneratedP286ExteriorDerivativeCoordinate
  rw [
    positiveP506MatterCurrentP286GaussCauchyState_connection_axis_zero,
    positiveP506MatterCurrentP286GaussCauchyState_connection_axis_zero]
  simp only [map_zero, p286CoordinateLieBracket_zero_left, sub_zero]
  rw [show
    p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286GaussCauchyState
          positiveP506MatterCurrentP286AxisContact pair) =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentP286GaussCauchyState.coframe
              positiveP506MatterCurrentP286AxisContact))
        positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate pair by
      exact congrFun
        positiveP506MatterCurrentP286_actionGeneratedCurvature_coordinate pair]
  rw [positiveP506MatterCurrentP286GaussCauchyState_coframe_axis,
    StageNineResidualLimitCoframeBalanceDecision.coframeGaugeSpacetimeHodgeLinear_one,
    liftGaugeTwoFormOperator_smul_operator_p286,
    positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate_normalForm]
  change
    c3h181StrongCouplingSquared •
        liftGaugeTwoFormOperator lorentzianCoframeHodge
          ![0, 0, 0,
            (1 / 3 : ℝ) •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
            0, 0] pair =
      ![(c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0, 0, 0, 0] pair
  rw [
    StageNineP286SourceAffineCurvatureJetNormalForm.liftGaugeTwoFormOperator_fixedHodge_apply_local]
  fin_cases pair <;> simp [c3h181StrongCouplingSquared, smul_smul]
  congr 1

theorem currentGaussCauchyState_gaugeConnection_zero :
    positiveP506MatterCurrentP286GaussCauchyState.gaugeConnection = 0 := by
  funext space direction
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gaugeConnection
        (canonicalCauchySlicePoint 0 space) direction = 0
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeConnection,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
  rfl

theorem currentGaussCauchyState_spatialConnectionDerivative_zero
    (space : StageNineSpatialPoint) (derivativeDirection : Fin 3)
    (formDirection : LorentzianIndex) :
    cauchyP286SpatialConnectionDerivativeCoordinate
        positiveP506MatterCurrentP286GaussCauchyState space
        derivativeDirection formDirection = 0 := by
  unfold cauchyP286SpatialConnectionDerivativeCoordinate
  have connectionFunctionZero :
      (fun candidate =>
        p286CoordinateEquiv
          (positiveP506MatterCurrentP286GaussCauchyState.gaugeConnection
            candidate formDirection)) = fun _ => 0 := by
    funext candidate
    rw [currentGaussCauchyState_gaugeConnection_zero]
    simp
  rw [connectionFunctionZero]
  simp

theorem currentActionGeneratedP286CurvatureCoordinate_normalForm :
    (fun pair =>
      p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286GaussCauchyState
          positiveP506MatterCurrentP286AxisContact pair)) =
      ![(c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0, 0, 0, 0] := by
  funext pair
  have exteriorDerivative := congrFun
    actionGeneratedP286ExteriorDerivativeCoordinate_normalForm pair
  unfold actionGeneratedP286ExteriorDerivativeCoordinate at exteriorDerivative
  rw [
    positiveP506MatterCurrentP286GaussCauchyState_connection_axis_zero,
    positiveP506MatterCurrentP286GaussCauchyState_connection_axis_zero]
    at exteriorDerivative
  simpa using exteriorDerivative

theorem currentActionGeneratedP286Curvature_pair_one_zero :
    actionGeneratedP286Curvature positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact 1 = 0 := by
  apply p286CoordinateEquiv.injective
  simpa using congrFun currentActionGeneratedP286CurvatureCoordinate_normalForm 1

theorem currentActionGeneratedP286Curvature_pair_zero_coordinate :
    p286CoordinateEquiv
        (actionGeneratedP286Curvature positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286GaussCauchyState
          positiveP506MatterCurrentP286AxisContact 0) =
      (c3h181StrongCouplingSquared / 3) •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  simpa using congrFun currentActionGeneratedP286CurvatureCoordinate_normalForm 0

theorem currentActionGeneratedP286Curvature_pair_two_zero :
    actionGeneratedP286Curvature positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact 2 = 0 := by
  apply p286CoordinateEquiv.injective
  simpa using congrFun currentActionGeneratedP286CurvatureCoordinate_normalForm 2

theorem positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift point =
      c3h181U7ConnectionNormalForm point := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeConnection]
  funext direction
  simp only [sourceGeneratedP286ActionLocalActualLift,
    sourceGeneratedP286ActionLocalConnection,
    p286CoordinateEquiv.apply_symm_apply]
  unfold sourceGeneratedP286ActionLocalConnectionCoordinate
  rw [currentGaussCauchyState_gaugeConnection_zero]
  simp only [Pi.zero_apply, map_zero, zero_add]
  unfold sourceGeneratedP286ActionLocalIncrement
  fin_cases direction
  all_goals simp [Fin.sum_univ_four,
    sourceGeneratedP286ActionLocalConnectionJet,
    currentGaussCauchyState_spatialConnectionDerivative_zero,
    sourceGeneratedP286SpatialConnectionVelocity_coordinate,
    currentGaussCauchyState_gaugeConnection_zero,
    currentActionGeneratedP286Curvature_pair_zero_coordinate,
    currentActionGeneratedP286Curvature_pair_one_zero,
    currentActionGeneratedP286Curvature_pair_two_zero,
    actionGeneratedP286ExteriorDerivativeCoordinate_normalForm,
    c3h181U7ConnectionNormalForm, temporalSpatialPair,
    canonicalLorentzianTimeDirection, localBaseCoordinate_apply,
    smul_smul]
  all_goals module

theorem currentUStar_gaugeConnection_eq_currentU7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeConnection =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection := by
  calc
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeConnection =
        positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeConnection :=
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeConnection
    _ = positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection :=
      positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeConnection
    _ = positiveP506MatterCurrentCompleteBaseActual.gaugeConnection :=
      positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeConnection
    _ = positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection :=
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeConnection

def c3h181FullConnectionNormalForm (point : BasePoint) : P286GaugeOneForm :=
  c3h181U7ConnectionNormalForm point +
    p286HolonomicSecondJetQuadraticRealization
      positiveP506MatterCurrentCompleteActionPrincipalSecondJet point

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual point =
      c3h181FullConnectionNormalForm point := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection]
  change
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual point = _
  unfold positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
    installP286HolonomicConnectionSecondJet
  rw [holonomicP286GaugeConnectionCoordinate_vary]
  simp only [one_smul]
  have backgroundCoordinateEq :
      holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift point =
        c3h181U7ConnectionNormalForm point := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [currentUStar_gaugeConnection_eq_currentU7]
    exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm
        point
  rw [backgroundCoordinateEq]
  rfl

theorem positiveActionGeneratedTemporalVelocityP286SecondJet_realization_normalForm
    (point : BasePoint) :
    p286HolonomicSecondJetQuadraticRealization
        positiveActionGeneratedTemporalVelocityP286SecondJet point =
      (c3h181StrongCouplingSquared / 2 *
          (point canonicalLorentzianTimeDirection) ^ 2) •
        canonicalP286SpatialGaugeOneForm
          positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity := by
  rw [p286HolonomicSecondJetQuadraticRealization_apply]
  unfold positiveActionGeneratedTemporalVelocityP286SecondJet
    p286TemporalVelocityActionSecondJet
    p286TemporalVelocityActionSecondJetAmbient
  change
    (1 / 2 : ℝ) •
        (c3h181StrongCouplingSquared •
          (point canonicalLorentzianTimeDirection •
            (point canonicalLorentzianTimeDirection •
              canonicalP286SpatialGaugeOneForm
                positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity))) =
      _
  module

def c3h181FullConnectionCoefficient
    (point : BasePoint) (direction : LorentzianIndex) : ℝ :=
  ![
    -(c3h181StrongCouplingSquared / 6) *
      ((point 1) ^ 2 + (point 2) ^ 2 + (point 3) ^ 2),
    c3h181StrongCouplingSquared / 3 *
      point canonicalLorentzianTimeDirection,
    0,
    -(c3h181StrongCouplingSquared / 2) *
      (point canonicalLorentzianTimeDirection) ^ 2
  ] direction

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point direction =
      c3h181FullConnectionCoefficient point direction •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  rw [congrFun
    (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm
      point) direction]
  unfold c3h181FullConnectionNormalForm
  rw [positiveP506MatterCurrentCompleteActionPrincipalSecondJet, map_add]
  simp only [Pi.add_apply]
  rw [positiveActionGeneratedTemporalVelocityP286SecondJet_realization_normalForm]
  unfold positiveActionGeneratedGaussRadialP286SecondJet
  rw [
    p286GaussRadialActionSecondJet_realization_normalForm,
    currentSpatialAuxiliaryVelocity_eq_thirdNegCharge,
    canonicalSpatialThirdOnly_eq_thirdGaugeOneForm]
  fin_cases direction <;>
    simp [c3h181FullConnectionCoefficient, c3h181U7ConnectionNormalForm,
      p286ThirdGaugeOneForm, p286TemporalGaugeOneForm,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  all_goals module

def c3h181U7ConnectionLinear :
    BasePoint →L[ℝ] P286GaugeOneForm :=
  (c3h181StrongCouplingSquared / 3) •
    (p286BaseCoordinate canonicalLorentzianTimeDirection).smulRight
      (fun direction : LorentzianIndex =>
        if direction = 1 then
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        else 0)

theorem c3h181U7ConnectionLinear_apply (point : BasePoint) :
    c3h181U7ConnectionLinear point = c3h181U7ConnectionNormalForm point := by
  funext direction
  by_cases directionOne : direction = 1
  · subst direction
    simp [c3h181U7ConnectionLinear, c3h181U7ConnectionNormalForm,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      smul_smul]
  · simp [c3h181U7ConnectionLinear, c3h181U7ConnectionNormalForm,
      ContinuousLinearMap.smulRight_apply, directionOne]

theorem c3h181U7ConnectionNormalForm_component_directionalDerivative
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => c3h181U7ConnectionNormalForm candidate formDirection)
        point derivativeDirection =
      c3h181U7ConnectionLinear (coordinateDirection derivativeDirection)
        formDirection := by
  let evaluation : P286GaugeOneForm →L[ℝ] P286CoordinateCarrier :=
    ContinuousLinearMap.proj formDirection
  let linear : BasePoint →L[ℝ] P286CoordinateCarrier :=
    evaluation.comp c3h181U7ConnectionLinear
  have functionEquality :
      (fun candidate =>
        c3h181U7ConnectionNormalForm candidate formDirection) = linear := by
    funext candidate
    change
      c3h181U7ConnectionNormalForm candidate formDirection =
        c3h181U7ConnectionLinear candidate formDirection
    rw [c3h181U7ConnectionLinear_apply]
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [linear.hasFDerivAt.fderiv]
  rfl

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_normalForm
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point derivativeDirection formDirection =
      c3h181U7ConnectionLinear (coordinateDirection derivativeDirection)
          formDirection +
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet.1 point
          (coordinateDirection derivativeDirection) formDirection := by
  have finalFunctionEquality :
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          candidate formDirection) =
        fun candidate =>
          holonomicP286GaugeConnectionCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
            candidate formDirection := by
    funext candidate
    unfold holonomicP286GaugeConnectionCoordinate
    rw [
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection]
  unfold p286GaugeConnectionCoordinateDerivative
  rw [finalFunctionEquality]
  change
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
        point derivativeDirection formDirection = _
  unfold positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
    installP286HolonomicConnectionSecondJet
  rw [p286GaugeConnectionCoordinateDerivative_vary_of_contDiff
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth
      (p286HolonomicSecondJetQuadraticRealization
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet)
      (p286HolonomicSecondJetQuadraticRealization_contDiff
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet),
    p286HolonomicSecondJetQuadraticRealization_variationDerivative]
  simp only [one_smul]
  have backgroundFunctionEquality :
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          candidate formDirection) =
        fun candidate =>
          c3h181U7ConnectionNormalForm candidate formDirection := by
    funext candidate
    unfold holonomicP286GaugeConnectionCoordinate
    rw [currentUStar_gaugeConnection_eq_currentU7]
    exact congrFun
      (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm
        candidate) formDirection
  unfold p286GaugeConnectionCoordinateDerivative
  rw [backgroundFunctionEquality,
    c3h181U7ConnectionNormalForm_component_directionalDerivative]
  rfl

theorem p286CoordinateLieBracket_self
    (component : P286CoordinateCarrier) :
    p286CoordinateLieBracket component component = 0 := by
  unfold p286CoordinateLieBracket p286LieBracket suLieBracket
  simp

theorem currentOriginAuxiliaryCoordinate_eq_gaussCauchy :
    positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate =
      positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate := by
  rfl

def c3h181FullCurvatureCoordinateNormalForm
    (point : BasePoint) : P286GaugeTwoForm :=
  ![
    (c3h181StrongCouplingSquared / 3 * (1 + point 1)) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
    (c3h181StrongCouplingSquared / 3 * point 2) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
    (c3h181StrongCouplingSquared / 3 * point 3 -
        c3h181StrongCouplingSquared *
          point canonicalLorentzianTimeDirection) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
    0, 0, 0
  ]

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point =
      c3h181FullCurvatureCoordinateNormalForm point := by
  funext pair
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_normalForm,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_normalForm,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateLieBracket_self]
  simp only [smul_zero, add_zero]
  fin_cases pair <;>
    simp [c3h181FullCurvatureCoordinateNormalForm,
      c3h181U7ConnectionLinear,
      positiveP506MatterCurrentCompleteActionPrincipalSecondJet,
      positiveActionGeneratedTemporalVelocityP286SecondJet,
      positiveActionGeneratedGaussRadialP286SecondJet,
      p286TemporalVelocityActionSecondJet,
      p286TemporalVelocityActionSecondJetAmbient,
      p286GaussRadialActionSecondJet,
      p286GaussRadialActionSecondJetAmbient,
      currentSpatialAuxiliaryVelocity_eq_thirdNegCharge,
      p286SpatialThirdOnly, p286TemporalGaugeOneForm,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      coordinateDirection, canonicalLorentzianTimeDirection,
      pairFirst, pairSecond, Fin.sum_univ_three,
      c3h181StrongCouplingSquared, smul_smul] <;>
    module

def c3h181FullAuxiliaryCoordinateNormalForm
    (point : BasePoint) : P286GaugeTwoForm :=
  ![
    0, 0, 0,
    ((1 / 3 : ℝ) * (1 + point 1)) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
    ((1 / 3 : ℝ) * point 2) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
    ((1 / 3 : ℝ) * point 3 -
        point canonicalLorentzianTimeDirection) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
  ]

theorem positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_normalForm
    (point : BasePoint) :
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point =
      c3h181FullAuxiliaryCoordinateNormalForm point := by
  unfold positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate
  rw [currentOriginAuxiliaryCoordinate_eq_gaussCauchy,
    positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate_normalForm,
    currentSpatialAuxiliaryVelocity_eq_thirdNegCharge]
  funext pair
  fin_cases pair <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      p286SpatialAuxiliaryVelocityEmbedding, p286SpatialThirdOnly,
      p286GaussRadialAuxiliaryProfile, p286GaussAuxiliaryAxisEmbedding,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three] <;>
    module

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_auxiliaryCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point =
      c3h181FullAuxiliaryCoordinateNormalForm point := by
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_auxiliaryCoordinate,
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_normalForm]

theorem c3h181FullAuxiliary_hodge_eq_curvature
    (point : BasePoint) :
    liftGaugeTwoFormOperator
        (c3h181StrongCouplingSquared •
          coframeGaugeSpacetimeHodgeLinear 1)
        (c3h181FullAuxiliaryCoordinateNormalForm point) =
      c3h181FullCurvatureCoordinateNormalForm point := by
  rw [liftGaugeTwoFormOperator_smul_operator_p286,
    StageNineResidualLimitCoframeBalanceDecision.coframeGaugeSpacetimeHodgeLinear_one]
  funext pair
  change
    c3h181StrongCouplingSquared •
        liftGaugeTwoFormOperator lorentzianCoframeHodge
          (c3h181FullAuxiliaryCoordinateNormalForm point) pair =
      c3h181FullCurvatureCoordinateNormalForm point pair
  rw [
    StageNineP286SourceAffineCurvatureJetNormalForm.liftGaugeTwoFormOperator_fixedHodge_apply_local]
  fin_cases pair <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      c3h181FullCurvatureCoordinateNormalForm,
      canonicalLorentzianTimeDirection, smul_smul] <;>
    module

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_coordinate
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
              point))
        (holonomicP286GaugeAuxiliaryCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          point) := by
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureCoordinate_normalForm,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_auxiliaryCoordinate_normalForm]
  exact (c3h181FullAuxiliary_hodge_eq_curvature point).symm

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation
    (point : BasePoint) :
    holonomicGaugeCurvature
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
              point))
        (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary
          point) := by
  funext pair
  apply p286CoordinateEquiv.injective
  rw [p286CoordinateEquiv_liftGaugeTwoFormOperator]
  exact congrFun
    (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_coordinate
      point) pair

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionCoordinate_origin_zero
    (direction : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        0 direction =
      0 := by
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line]
  fin_cases direction <;>
    simp [c3h181FullConnectionCoefficient,
      canonicalLorentzianTimeDirection]

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_diagonal_zero
    (direction : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        0 direction direction =
      0 := by
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_normalForm]
  fin_cases direction <;>
    simp [c3h181U7ConnectionLinear,
      positiveP506MatterCurrentCompleteActionPrincipalSecondJet,
      positiveActionGeneratedTemporalVelocityP286SecondJet,
      positiveActionGeneratedGaussRadialP286SecondJet,
      p286TemporalVelocityActionSecondJet,
      p286TemporalVelocityActionSecondJetAmbient,
      p286GaussRadialActionSecondJet,
      p286GaussRadialActionSecondJetAmbient,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      coordinateDirection, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalar_vacuum :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar = _
  change
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.scalar = _
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_biradial :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe =
      fun _ => biradialCoframe 1 1 := by
  funext point
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one,
    biradialCoframe_one_one]

theorem c3h181CanonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem fullSynchronizedActionResponseOperator_conjugateMatter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).conjugateMatter 0 =
      current.conjugateMatter 0 := by
  change
    actionGeneratedConjugateMatterLocalField
        (fullSynchronizedActionMatterCauchyState source current) 0 0 =
      current.conjugateMatter 0
  rw [actionGeneratedConjugateMatterLocalField_origin]
  unfold fullSynchronizedActionMatterCauchyState
    canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual source current).conjugateMatter
        (canonicalCauchySlicePoint 0 0) =
      current.conjugateMatter 0
  rw [c3h181CanonicalCauchySlicePoint_zero_zero]
  rfl

theorem positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_conjugate_origin_current :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
        0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  calc
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
          0 =
        positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter
          0 := rfl
    _ = positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
          0 :=
      positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin
    _ = positiveP506MatterCurrentCompleteBaseActual.conjugateMatter 0 := rfl
    _ =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.conjugateMatter
          0 :=
      congrFun
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.2
        0
    _ = _ :=
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_conjugate_origin :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.conjugateMatter
        0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  rw [show
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual =
      fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual by rfl]
  rw [fullSynchronizedActionResponseOperator_conjugateMatter_origin]
  change
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
        0 = _
  exact
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_conjugate_origin_current

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarCovariantDerivative_eq_fixedVacuumAction
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point direction =
      scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarCovariantDerivative
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  unfold holonomicP286GaugeConnectionCoordinate
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeConnection
            point direction))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeConnection
                point direction))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rw [p286CoordinateEquiv.symm_apply_apply]

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarCovariantDerivative_origin_zero
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        0 direction =
      0 := by
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarCovariantDerivative_eq_fixedVacuumAction,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionCoordinate_origin_zero]
  simp

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarCovariantDerivative_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point direction)
        0 direction =
      0 := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    holonomicP286GaugeConnectionCoordinate
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
      point direction
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    have smooth :=
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_smooth
        |>.2.2.2.2.1 direction
    simpa [connection, holonomicP286GaugeConnectionCoordinate] using
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
  rw [show
    (fun point =>
      holonomicScalarCovariantDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point direction) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarCovariantDerivative_eq_fixedVacuumAction
        point direction]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  change
    scalarP286ActionBilinear
        (p286GaugeConnectionCoordinateDerivative
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          0 direction direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      0
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_diagonal_zero]
  simp

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarDivergence_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        direction 0 =
      0 := by
  apply scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
      (a := 1) (b := 1)
  · norm_num
  · norm_num
  · exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_biradial
  · intro formDirection
    exact
      ((holonomicScalarCovariantDerivative_contDiff
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_smooth
        formDirection).differentiable (by simp)).differentiableAt
  · exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarCovariantDerivative_diagonalDerivative_zero

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarKineticAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          0)
        (holonomicScalarVariationAlgebraicDirection
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          direction 0) =
      0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeOrigin :
      (toContinuumPointField
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        0).scalarCovariantDerivative =
        0 := by
    funext formDirection
    exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarCovariantDerivative_origin_zero
        formDirection
  rw [covariantDerivativeOrigin]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarPotential_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          0)
        direction =
      0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
      0).scalar =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    exact congrFun
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalar_vacuum
      0]
  simp

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarYukawa_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          0)
        direction =
      0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  rw [show
    (toContinuumPointField
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
      0).conjugateMatter = diracSpinZeroMatterCoordinate by
    exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_conjugate_origin,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  norm_num

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        direction 0 =
      0 := by
  unfold scalarAlgebraicDirectionalCoefficient
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarKineticAlgebraic_origin_zero,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarPotential_origin_zero,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarYukawa_origin_zero]
  ring

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarEuler_origin
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        direction 0 =
      0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarAlgebraic_origin_zero,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarDivergence_origin_zero]
  ring

/-! ## C3h181 no-premise closure bundle -/

/-- The complete local C3h181 checkpoint.  The P286 equation is explicitly
classified as producer soundness; only the scalar Euler equation is an
independent constraint at this checkpoint. -/
structure
    PositiveP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLaw :
    Prop where
  actionPrincipalFirstGerm :
    PositiveP506MatterCurrentP286CompleteActionPrincipalFirstGermFullSynchronizedLocalActualLaw
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization.canonicalP506SourceAffineL0ObservableLineageReference
  currentChargeIdentified :
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge =
      positiveP506MatterCurrentGravityCoupledP286GaussCharge
  currentVelocityIdentified :
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity =
      p286SpatialThirdOnly
        (-positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
  synchronizedSmooth :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.Smooth
  synchronizedNondegenerate :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.Nondegenerate
  connectionOnGeneratedChargeLine :
    ∀ point : BasePoint, ∀ direction : LorentzianIndex,
      holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          point direction =
        c3h181FullConnectionCoefficient point direction •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
  structuralP286Bianchi :
    ∀ point : BasePoint, ∀ first second third : LorentzianIndex,
      covariantCurvatureDerivative
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point first second third +
          covariantCurvatureDerivative
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point second third first +
          covariantCurvatureDerivative
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point third first second =
        0
  producerP286AuxiliaryFullDomainConsistency :
    ∀ point : BasePoint,
      holonomicGaugeCurvature
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          point =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear
              (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
                point))
          (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary
            point)
  independentScalarConstraintAtOrigin :
    ∀ direction : ScalarCoordinateCarrier,
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          direction 0 =
        0

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_realizes_C3h181 :
    PositiveP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLaw := by
  exact
    { actionPrincipalFirstGerm :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_realizes_C3h180
      exactP506L0Lineage :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_realizes_C3h180.exactP506L0Lineage
      currentChargeIdentified := currentGaussCharge_eq_priorGaussCharge
      currentVelocityIdentified :=
        currentSpatialAuxiliaryVelocity_eq_thirdNegCharge
      synchronizedSmooth :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_smooth
      synchronizedNondegenerate :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_nondegenerate
      connectionOnGeneratedChargeLine :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      structuralP286Bianchi :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286Bianchi
      producerP286AuxiliaryFullDomainConsistency :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation
      independentScalarConstraintAtOrigin :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_scalarEuler_origin }


end

end SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
