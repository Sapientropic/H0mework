import H0mework.Physics.ConnectionJets.P286GaussRadialSecondJetLift
import H0mework.Physics.ConnectionJets.P286TemporalVelocitySecondJetLift
import H0mework.Physics.MatterCurrent.P286AffineCurvatureFirstJetBoundary
import H0mework.Physics.Exterior.FullSynchronizedActionResponseOperator

/-!
# C3h180: complete action-principal P286 first-germ actual

This module combines the two second jets generated directly by the complete
P286 action response: the physical-time velocity sector and the equal-axis
radial Gauss sector.  The old affine `U*` curvature first jet is proved zero
independently, so the two action-owned sectors can be installed without
subtracting a residual or choosing a quotient representative.

After installation the complete full-synchronized action operator is run
again.  It recomputes the gravity and matter response while preserving the
primitive P286 connection and auxiliary fields.  The resulting whole actual
therefore closes all four directions of the P286 auxiliary-equation first
germ on the same contact.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286Bianchi
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineP286GaussRadialSecondJetLift
open StageNineSourceActionGeneratedP506MatterCurrentP286AffineCurvatureFirstJetBoundary
open StageNineP286TemporalVelocitySecondJetLift
open SU7MotherLieAlgebra

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

private abbrev UStar : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift

private abbrev sourceStrongCouplingSquared : ℝ :=
  ((sourceGeneratedUnifiedCouplings
    positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)

private abbrev actionGeneratedVelocity : P286SpatialGaugeDirection :=
  positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity

private abbrev actionGeneratedCharge : P286CoordinateCarrier :=
  positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge

/-! ## The complete auxiliary first jet consumed by the action -/

def positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear :
    BasePoint →L[ℝ] P286GaugeTwoForm :=
  (p286BaseCoordinate canonicalLorentzianTimeDirection).smulRight
      (p286SpatialAuxiliaryVelocityEmbedding actionGeneratedVelocity) +
    p286GaussRadialAuxiliaryFirstJetLinear actionGeneratedCharge

theorem positiveP506MatterCurrentCompleteResponseAuxiliaryCoordinate_eq_origin_add_firstJet
    (point : BasePoint) :
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point =
      positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate +
        positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear point := by
  unfold positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate
  rw [p286GaussRadialAuxiliaryProfile_eq_firstJetLinear]
  funext pair
  simp [positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear,
    ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply]
  abel

theorem positiveP506MatterCurrentCompleteResponseAuxiliaryCoordinate_firstJet
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate 0
        derivativeDirection =
      positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear
        (coordinateDirection derivativeDirection) := by
  rw [show positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate =
      fun point =>
        positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate +
          positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear point by
    funext point
    exact
      positiveP506MatterCurrentCompleteResponseAuxiliaryCoordinate_eq_origin_add_firstJet
        point]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_add,
    positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear.hasFDerivAt.fderiv]

theorem positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear_time :
    positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear
        (coordinateDirection canonicalLorentzianTimeDirection) =
      p286SpatialAuxiliaryVelocityEmbedding actionGeneratedVelocity := by
  simp [positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear,
    p286GaussRadialAuxiliaryFirstJetLinear,
    ContinuousLinearMap.smulRight_apply,
    p286BaseCoordinate_apply, coordinateDirection,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three]

theorem positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear_spatial
    (axis : Fin 3) :
    positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear
        (coordinateDirection axis.succ) =
      fieldDirectionalDerivative
        (p286GaussRadialAuxiliaryProfile actionGeneratedCharge) 0 axis.succ := by
  rw [p286GaussRadialAuxiliaryProfile_spatialFirstJet]
  fin_cases axis <;>
    simp [positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear,
      p286GaussRadialAuxiliaryFirstJetLinear,
      ContinuousLinearMap.smulRight_apply,
      p286BaseCoordinate_apply, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-! ## Exact source/action second-jet sectors -/

/-- The temporal sector is fixed by the action-generated velocity and the
source-generated strong coupling. -/
def positiveActionGeneratedTemporalVelocityP286SecondJet :
    P286HolonomicConnectionSecondJet :=
  p286TemporalVelocityActionSecondJet sourceStrongCouplingSquared
    actionGeneratedVelocity

theorem positiveActionGeneratedTemporalVelocityP286SecondJet_timeResponse :
    p286HolonomicSecondJetCurvatureSymbol
        positiveActionGeneratedTemporalVelocityP286SecondJet
        canonicalLorentzianTimeDirection =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (p286SpatialAuxiliaryVelocityEmbedding actionGeneratedVelocity) :=
  p286TemporalVelocityActionSecondJet_curvatureSymbol_time _ _

theorem positiveActionGeneratedTemporalVelocityP286SecondJet_spatialResponse
    (axis : Fin 3) :
    p286HolonomicSecondJetCurvatureSymbol
        positiveActionGeneratedTemporalVelocityP286SecondJet axis.succ = 0 :=
  p286TemporalVelocityActionSecondJet_curvatureSymbol_spatial _ _ axis

/-- The radial sector is fixed by the action-generated Gauss charge and the
same source coupling. -/
def positiveActionGeneratedGaussRadialP286SecondJet :
    P286HolonomicConnectionSecondJet :=
  p286GaussRadialActionSecondJet sourceStrongCouplingSquared
    actionGeneratedCharge

/-! ## Complete action-generated second jet -/

/-- The two independent action sectors are added before realization.  No
coefficient, endpoint, residual, or branch is exposed to a caller. -/
def positiveP506MatterCurrentCompleteActionPrincipalSecondJet :
    P286HolonomicConnectionSecondJet :=
  positiveActionGeneratedTemporalVelocityP286SecondJet +
    positiveActionGeneratedGaussRadialP286SecondJet

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJet_timeResponse :
    p286HolonomicSecondJetCurvatureSymbol
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet
        canonicalLorentzianTimeDirection =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (p286SpatialAuxiliaryVelocityEmbedding actionGeneratedVelocity) := by
  rw [positiveP506MatterCurrentCompleteActionPrincipalSecondJet, map_add]
  simp only [Pi.add_apply]
  rw [positiveActionGeneratedTemporalVelocityP286SecondJet_timeResponse]
  change
    liftGaugeTwoFormOperator
          (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
          (p286SpatialAuxiliaryVelocityEmbedding actionGeneratedVelocity) +
        p286HolonomicSecondJetCurvatureSymbol
          (p286GaussRadialActionSecondJet sourceStrongCouplingSquared
            actionGeneratedCharge)
          canonicalLorentzianTimeDirection = _
  rw [p286GaussRadialActionSecondJet_curvatureSymbol_time, add_zero]

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJet_spatialResponse
    (axis : Fin 3) :
    p286HolonomicSecondJetCurvatureSymbol
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet axis.succ =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (fieldDirectionalDerivative
          (p286GaussRadialAuxiliaryProfile actionGeneratedCharge)
          0 axis.succ) := by
  rw [positiveP506MatterCurrentCompleteActionPrincipalSecondJet, map_add]
  simp only [Pi.add_apply]
  rw [positiveActionGeneratedTemporalVelocityP286SecondJet_spatialResponse,
    zero_add]
  exact p286GaussRadialActionSecondJet_curvatureSymbol_eq_auxiliaryFirstJet
    sourceStrongCouplingSquared actionGeneratedCharge axis

/-! ## Same-actual installation and synchronized response -/

def positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual :
    StageNineHolonomicConfiguration :=
  installP286HolonomicConnectionSecondJet UStar
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1

/-- Whole response actual: gravity and matter are regenerated only after the
primitive P286 action-principal connection has been installed. -/
def positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual :
    StageNineHolonomicConfiguration :=
  fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_gaugeAuxiliary :
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual.gaugeAuxiliary =
      UStar.gaugeAuxiliary :=
  rfl

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeAuxiliary :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary =
      UStar.gaugeAuxiliary := by
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual,
    fullSynchronizedActionResponseOperator_gaugeAuxiliary,
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_gaugeAuxiliary]

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeConnection =
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual.gaugeConnection := by
  exact fullSynchronizedActionResponseOperator_gaugeConnection _ _

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one
    (point : BasePoint) :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
        point = 1 := by
  change UStar.coframe point = 1
  exact
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
      point

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_auxiliaryCoordinate
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point =
      positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeAuxiliary]
  change
    holonomicP286GaugeAuxiliaryCoordinate
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift point = _
  exact
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_auxiliaryCoordinate
      point

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_smooth :
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual.Smooth := by
  exact installP286HolonomicConnectionSecondJet_smooth UStar
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_smooth :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.Smooth := by
  exact fullSynchronizedActionResponseOperator_smooth
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_smooth

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_nondegenerate :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.Nondegenerate := by
  apply fullSynchronizedActionResponseOperator_nondegenerate
  intro point
  change Matrix.det (UStar.coframe point) ≠ 0
  exact
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_nondegenerate
      point

/-- Structural Bianchi identity of the generated holonomic connection.  This
is an off-shell identity and is deliberately not counted as an independent
field-equation closure. -/
theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286Bianchi
    (point : BasePoint) (first second third : LorentzianIndex) :
    covariantCurvatureDerivative
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          point first second third +
        covariantCurvatureDerivative
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          point second third first +
        covariantCurvatureDerivative
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          point third first second =
      0 :=
  holonomicP286GaugeCurvature_bianchi
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_smooth
    point first second third

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_connection_origin :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual 0 =
      holonomicP286GaugeConnectionCoordinate UStar 0 := by
  exact installP286HolonomicConnectionSecondJet_connection_origin UStar
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_firstJet_origin
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual 0
        derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative UStar 0
        derivativeDirection formDirection := by
  exact installP286HolonomicConnectionSecondJet_firstJet_origin UStar
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1
    derivativeDirection formDirection

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_curvature_origin :
    holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual 0 =
      holonomicP286GaugeCurvatureCoordinate UStar 0 := by
  exact installP286HolonomicConnectionSecondJet_curvature_origin UStar
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_origin :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
      holonomicP286GaugeConnectionCoordinate UStar 0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_connection_origin

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_firstJet_origin
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0
        derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative UStar 0
        derivativeDirection formDirection := by
  unfold p286GaugeConnectionCoordinateDerivative
    holonomicP286GaugeConnectionCoordinate
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_firstJet_origin
      derivativeDirection formDirection

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvature_origin :
    holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
      holonomicP286GaugeCurvatureCoordinate UStar 0 := by
  funext pair
  unfold holonomicP286GaugeCurvatureCoordinate holonomicGaugeCurvature
    p286ConnectionDerivative
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection]
  exact congrFun
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_curvature_origin
    pair

/-- The newly generated whole actual retains the already generated origin
auxiliary equation.  This is constructor soundness: the second jet changes
the curvature first germ while preserving the connection one-jet, curvature,
coframe, and auxiliary value at the common contact. -/
theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_origin :
    holonomicGaugeCurvature
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
              0))
        (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary
          0) := by
  have curvatureEq :
      holonomicGaugeCurvature
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
        holonomicGaugeCurvature UStar 0 := by
    funext pair
    apply p286CoordinateEquiv.injective
    exact congrFun
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvature_origin
      pair
  have coframeEq :
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe 0 =
        UStar.coframe 0 := by
    rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one,
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one]
  have auxiliaryEq :
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary 0 =
        UStar.gaugeAuxiliary 0 := by
    exact congrFun
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeAuxiliary
      0
  calc
    holonomicGaugeCurvature
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
      holonomicGaugeCurvature UStar 0 := curvatureEq
    _ =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear (UStar.coframe 0))
          (UStar.gaugeAuxiliary 0) :=
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_p286AuxiliaryEquation_origin
    _ =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear
              (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
                0))
          (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary
            0) := by rw [coframeEq, auxiliaryEq]

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_curvatureFirstJet_time
    (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
            point pair)
        0 canonicalLorentzianTimeDirection =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (p286SpatialAuxiliaryVelocityEmbedding actionGeneratedVelocity) pair := by
  unfold positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
  rw [installP286HolonomicConnectionSecondJet_curvatureDirectionalDerivative_origin
    UStar positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1
    canonicalLorentzianTimeDirection pair]
  rw [positiveP506MatterCurrentUStar_curvatureFirstJet_zero]
  simp only [zero_add, one_smul]
  exact congrFun
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet_timeResponse pair

theorem positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_curvatureFirstJet_spatial
    (axis : Fin 3) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
            point pair)
        0 axis.succ =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (fieldDirectionalDerivative
          (p286GaussRadialAuxiliaryProfile actionGeneratedCharge)
          0 axis.succ) pair := by
  unfold positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
  rw [installP286HolonomicConnectionSecondJet_curvatureDirectionalDerivative_origin
    UStar positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1 axis.succ pair]
  rw [positiveP506MatterCurrentUStar_curvatureFirstJet_zero]
  simp only [zero_add, one_smul]
  exact congrFun
    (positiveP506MatterCurrentCompleteActionPrincipalSecondJet_spatialResponse
      axis) pair

private theorem fullSynchronized_curvature_section_eq_secondJetActual
    (pair : Fin 6) :
    (fun point =>
      holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        point pair) =
      fun point =>
        holonomicP286GaugeCurvatureCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual
          point pair := by
  funext point
  unfold holonomicP286GaugeCurvatureCoordinate holonomicGaugeCurvature
    p286ConnectionDerivative
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection]

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureFirstJet_time
    (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point pair)
        0 canonicalLorentzianTimeDirection =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (p286SpatialAuxiliaryVelocityEmbedding actionGeneratedVelocity) pair := by
  rw [fullSynchronized_curvature_section_eq_secondJetActual]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_curvatureFirstJet_time
      pair

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureFirstJet_spatial
    (axis : Fin 3) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point pair)
        0 axis.succ =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (fieldDirectionalDerivative
          (p286GaussRadialAuxiliaryProfile actionGeneratedCharge)
          0 axis.succ) pair := by
  rw [fullSynchronized_curvature_section_eq_secondJetActual]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_curvatureFirstJet_spatial
      axis pair

/-- Complete four-direction first-germ closure against the unchanged actual
`U8.B` field.  This is producer soundness for the action-principal solve, not
an independent Euler--Lagrange constraint. -/
theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureFirstJet
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point pair)
        0 derivativeDirection =
      liftGaugeTwoFormOperator
        (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
        (fieldDirectionalDerivative
          positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate
          0 derivativeDirection) pair := by
  rw [positiveP506MatterCurrentCompleteResponseAuxiliaryCoordinate_firstJet]
  refine Fin.cases ?_ (fun axis => ?_) derivativeDirection
  · change
      fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate
              positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
              point pair)
          0 canonicalLorentzianTimeDirection =
        liftGaugeTwoFormOperator
          (sourceStrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
          (positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear
            (coordinateDirection canonicalLorentzianTimeDirection)) pair
    rw [positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear_time]
    exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureFirstJet_time
        pair
  · rw [positiveP506MatterCurrentCompleteAuxiliaryFirstJetLinear_spatial axis]
    exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureFirstJet_spatial
        axis pair

/-- Same-actual form of the complete first-germ law.  Both sides now read
fields from the final synchronized actual itself; the named U8 coordinate is
used only internally to prove that this actual preserved the source/action
generated auxiliary germ. -/
theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_firstGerm
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
            point pair)
        0 derivativeDirection =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
              0))
        (fieldDirectionalDerivative
          (holonomicP286GaugeAuxiliaryCoordinate
            positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual)
          0 derivativeDirection) pair := by
  have auxiliaryFunctionEq :
      holonomicP286GaugeAuxiliaryCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual =
        positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate := by
    funext point
    exact
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_auxiliaryCoordinate
        point
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one,
    auxiliaryFunctionEq]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureFirstJet
      derivativeDirection pair

/-! ## No-premise complete first-germ producer law -/

/-- C3h180's positive frontier.  The exact P506/L0 action graph first owns
`V`, `Q`, and `g²`; these data generate one closed symmetric connection second
jet and then one whole synchronized actual.  The final field proves the
complete four-direction/six-pair auxiliary first-germ response on that same
actual.  Equation readback is recorded as producer soundness, not as a new
independent Euler--Lagrange constraint. -/
structure
    PositiveP506MatterCurrentP286CompleteActionPrincipalFirstGermFullSynchronizedLocalActualLaw :
    Prop where
  sourceGeneratedUStar :
    PositiveP506MatterCurrentFullSynchronizedResponseProducerSoundnessLaw
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization.canonicalP506SourceAffineL0ObservableLineageReference
  velocityActionResponse :
    p286SpatialBFLegendreDualOperator
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget
  velocityActionResponseUnique : ∀ candidate : P286SpatialGaugeDirection,
    p286SpatialBFLegendreDualOperator candidate =
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget →
      candidate =
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity
  chargeActionResponse : ∀ component : P286CoordinateCarrier,
    p286CoordinateLiePairing
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge component =
      positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget component
  chargeActionResponseUnique : ∀ candidate : P286CoordinateCarrier,
    (∀ component,
      p286CoordinateLiePairing candidate component =
        positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
          component) →
      candidate = positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
  generatedSecondJet :
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet =
      p286TemporalVelocityActionSecondJet sourceStrongCouplingSquared
          actionGeneratedVelocity +
        p286GaussRadialActionSecondJet sourceStrongCouplingSquared
          actionGeneratedCharge
  generatedWholeActual :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual =
      fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        (installP286HolonomicConnectionSecondJet UStar
          positiveP506MatterCurrentCompleteActionPrincipalSecondJet 1)
  primitiveGaugeConnectionPreserved :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeConnection =
      positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual.gaugeConnection
  primitiveGaugeAuxiliaryPreserved :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary =
      UStar.gaugeAuxiliary
  synchronizedSmooth :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.Smooth
  synchronizedNondegenerate :
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.Nondegenerate
  connectionOriginFaithful :
    holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
      holonomicP286GaugeConnectionCoordinate UStar 0
  connectionFirstJetOriginFaithful :
    ∀ derivativeDirection formDirection : LorentzianIndex,
      p286GaugeConnectionCoordinateDerivative
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0
          derivativeDirection formDirection =
        p286GaugeConnectionCoordinateDerivative UStar 0
          derivativeDirection formDirection
  curvatureOriginFaithful :
    holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
      holonomicP286GaugeCurvatureCoordinate UStar 0
  producerP286AuxiliaryConsistency :
    holonomicGaugeCurvature
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
              0))
        (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.gaugeAuxiliary
          0)
  producerP286AuxiliaryFirstGermConsistency :
    ∀ derivativeDirection : LorentzianIndex, ∀ pair : Fin 6,
      fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate
              positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
              point pair)
          0 derivativeDirection =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear
              (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual.coframe
                0))
          (fieldDirectionalDerivative
            (holonomicP286GaugeAuxiliaryCoordinate
              positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual)
            0 derivativeDirection) pair

theorem positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_realizes_C3h180 :
    PositiveP506MatterCurrentP286CompleteActionPrincipalFirstGermFullSynchronizedLocalActualLaw := by
  exact
    { sourceGeneratedUStar :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_producerSoundness
      exactP506L0Lineage :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_producerSoundness.exactP506L0Lineage
      velocityActionResponse :=
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_response
      velocityActionResponseUnique := fun candidate response =>
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_unique
          candidate response
      chargeActionResponse :=
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response
      chargeActionResponseUnique := fun candidate response =>
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_unique
          candidate response
      generatedSecondJet := rfl
      generatedWholeActual := rfl
      primitiveGaugeConnectionPreserved :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeConnection
      primitiveGaugeAuxiliaryPreserved :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_gaugeAuxiliary
      synchronizedSmooth :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_smooth
      synchronizedNondegenerate :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_nondegenerate
      connectionOriginFaithful :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_origin
      connectionFirstJetOriginFaithful :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_firstJet_origin
      curvatureOriginFaithful :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvature_origin
      producerP286AuxiliaryConsistency :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_origin
      producerP286AuxiliaryFirstGermConsistency :=
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_p286AuxiliaryEquation_firstGerm }

end

end SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
