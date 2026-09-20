import H0mework.Physics.Coframe.CoframeNativeMatterOriginActionWrite
import H0mework.Physics.Coframe.CoframeNativeConjugateMatterFrameAction

/-!
# Coframe-native conjugate-matter origin action write

The current coframe turns the action-generated internal frame-time adjoint
response into the coordinate first jet `e⁰_μ r`.  The resulting actual keeps
the conjugate field value and every other primitive field, while its frame
time derivative is the branch-free action solve.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeConjugateMatterOriginActionWrite

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineCoframeNativeMatterFrameAction
open StageNineCoframeNativeMatterOriginActionWrite
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineP286ActionCauchySplit
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## The coframe-row dual first-jet installer -/

/-- Linear dual-coordinate write with derivative
`δ(∂_μ λ) = e⁰_μ r`. -/
def coframeRowLinearConjugateMatterCoordinateWrite
    (coframe : LorentzianCoframe)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  coframeRowLinearFunctional coframe point • matterDualCoordinates response

@[simp] theorem coframeRowLinearConjugateMatterCoordinateWrite_origin
    (coframe : LorentzianCoframe)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    coframeRowLinearConjugateMatterCoordinateWrite coframe response 0 = 0 := by
  simp [coframeRowLinearConjugateMatterCoordinateWrite]

theorem coframeRowLinearConjugateMatterCoordinateWrite_directionalDerivative
    (coframe : LorentzianCoframe)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (coframeRowLinearConjugateMatterCoordinateWrite coframe response)
        point direction =
      matterDualCoordinates ((coframe 0 direction : ℂ) • response) := by
  have derivative :=
    (coframeRowLinearFunctional coframe).hasFDerivAt (x := point)
      |>.smul_const (matterDualCoordinates response)
  unfold fieldDirectionalDerivative
    coframeRowLinearConjugateMatterCoordinateWrite
  rw [derivative.fderiv]
  change
    coframeRowLinearFunctional coframe (coordinateDirection direction) •
        matterDualCoordinates response =
      matterDualCoordinates ((coframe 0 direction : ℂ) • response)
  rw [coframeRowLinearFunctional_coordinateDirection,
    matterDualCoordinates_smul]
  rfl

theorem coframeRowLinearConjugateMatterCoordinateWrite_contDiff
    (coframe : LorentzianCoframe)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞
      (coframeRowLinearConjugateMatterCoordinateWrite coframe response) :=
  (coframeRowLinearFunctional coframe).contDiff.smul contDiff_const

/-- A dual response occupying the internal frame-time slot. -/
def frameTimeOnlyConjugateMatterResponse
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    ConjugateMatterDerivativeFamily :=
  fun internal => if internal = 0 then response else 0

/-- Coordinate expression of the frame-time-only response. -/
def coframeRowCoordinateConjugateMatterResponse
    (coframe : LorentzianCoframe)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    ConjugateMatterDerivativeFamily :=
  fun coordinate => (coframe 0 coordinate : ℂ) • response

theorem coordinateConjugateMatterDerivative_frameTimeOnly
    (coframe : LorentzianCoframe)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    coordinateConjugateMatterDerivative coframe
        (frameTimeOnlyConjugateMatterResponse response) =
      coframeRowCoordinateConjugateMatterResponse coframe response := by
  funext coordinate
  unfold coordinateConjugateMatterDerivative
    frameTimeOnlyConjugateMatterResponse
    coframeRowCoordinateConjugateMatterResponse
  rw [Finset.sum_eq_single (0 : LorentzianIndex)]
  · simp
  · intro candidate _ candidateNe
    simp [candidateNe]
  · simp

theorem frameConjugateMatterDerivative_coframeRowCoordinateResponse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    frameConjugateMatterDerivative coframe
        (coframeRowCoordinateConjugateMatterResponse coframe response) =
      frameTimeOnlyConjugateMatterResponse response := by
  rw [← coordinateConjugateMatterDerivative_frameTimeOnly]
  exact frameConjugateMatterDerivative_coordinateConjugateMatterDerivative
    coframe nondegenerate (frameTimeOnlyConjugateMatterResponse response)

theorem frameConjugateMatterDerivative_add_coframeRowResponse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coordinateDerivative : ConjugateMatterDerivativeFamily)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    frameConjugateMatterDerivative coframe
        (fun coordinate =>
          coordinateDerivative coordinate +
            coframeRowCoordinateConjugateMatterResponse coframe response
              coordinate) =
      fun internal =>
        frameConjugateMatterDerivative coframe coordinateDerivative internal +
          frameTimeOnlyConjugateMatterResponse response internal := by
  funext internal
  unfold frameConjugateMatterDerivative
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  exact congrFun
    (frameConjugateMatterDerivative_coframeRowCoordinateResponse
      coframe nondegenerate response) internal

/-- Install one generated frame-time dual response while retaining the other
eight primitive fields. -/
def installCoframeRowConjugateMatterResponse
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  varyConjugateMatterCoordinates current
    (coframeRowLinearConjugateMatterCoordinateWrite
      (current.coframe 0) response) 1

@[simp] theorem installCoframeRowConjugateMatterResponse_coframe
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response).coframe =
      current.coframe := rfl

@[simp] theorem installCoframeRowConjugateMatterResponse_gravityConnection
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response
      ).gravityConnection = current.gravityConnection := rfl

@[simp] theorem installCoframeRowConjugateMatterResponse_gravityAuxiliary
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response
      ).gravityAuxiliary = current.gravityAuxiliary := rfl

@[simp] theorem
    installCoframeRowConjugateMatterResponse_gravitySimplicityMultiplier
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response
      ).gravitySimplicityMultiplier = current.gravitySimplicityMultiplier := rfl

@[simp] theorem installCoframeRowConjugateMatterResponse_gaugeConnection
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response
      ).gaugeConnection = current.gaugeConnection := rfl

@[simp] theorem installCoframeRowConjugateMatterResponse_gaugeAuxiliary
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response
      ).gaugeAuxiliary = current.gaugeAuxiliary := rfl

@[simp] theorem installCoframeRowConjugateMatterResponse_scalar
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response).scalar =
      current.scalar := rfl

@[simp] theorem installCoframeRowConjugateMatterResponse_matter
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response).matter =
      current.matter := rfl

/-- The adjoint row write does not alter the primal covariant derivative. -/
@[simp] theorem
    holonomicMatterCovariantDerivative_installCoframeRowConjugateMatterResponse
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) :
    holonomicMatterCovariantDerivative
        (installCoframeRowConjugateMatterResponse current response) point =
      holonomicMatterCovariantDerivative current point := by
  rfl

theorem installCoframeRowConjugateMatterResponse_coordinates
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) :
    holonomicConjugateMatterCoordinates
        (installCoframeRowConjugateMatterResponse current response) point =
      holonomicConjugateMatterCoordinates current point +
        coframeRowLinearConjugateMatterCoordinateWrite
          (current.coframe 0) response point := by
  apply PiLp.ext
  intro index
  simp [holonomicConjugateMatterCoordinates,
    installCoframeRowConjugateMatterResponse,
    varyConjugateMatterCoordinates, matterDualCoordinates,
    matterDualOfCoordinates_basis_apply]

@[simp] theorem installCoframeRowConjugateMatterResponse_origin
    (current : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response
      ).conjugateMatter 0 = current.conjugateMatter 0 := by
  apply matterDualCoordinates_injective
  simpa [holonomicConjugateMatterCoordinates] using
    installCoframeRowConjugateMatterResponse_coordinates current response 0

theorem
    installCoframeRowConjugateMatterResponse_coordinateDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (installCoframeRowConjugateMatterResponse current response)
        0 direction =
      holonomicConjugateMatterDerivativeCoordinates current 0 direction +
        matterDualCoordinates
          ((current.coframe 0 0 direction : ℂ) • response) := by
  have responseDifferentiable : DifferentiableAt ℝ
      (coframeRowLinearConjugateMatterCoordinateWrite
        (current.coframe 0) response) 0 :=
    (coframeRowLinearConjugateMatterCoordinateWrite_contDiff
      (current.coframe 0) response).differentiable (by simp)
      |>.differentiableAt
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  rw [show
    holonomicConjugateMatterCoordinates
        (installCoframeRowConjugateMatterResponse current response) =
      holonomicConjugateMatterCoordinates current +
        coframeRowLinearConjugateMatterCoordinateWrite
          (current.coframe 0) response by
    funext point
    exact installCoframeRowConjugateMatterResponse_coordinates
      current response point]
  rw [fderiv_add conjugateDifferentiable responseDifferentiable, add_apply]
  change
    _ + fieldDirectionalDerivative
          (coframeRowLinearConjugateMatterCoordinateWrite
            (current.coframe 0) response) 0 direction = _
  rw [coframeRowLinearConjugateMatterCoordinateWrite_directionalDerivative]

theorem installCoframeRowConjugateMatterResponse_derivativeDual_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (installCoframeRowConjugateMatterResponse current response)
        0 direction =
      holonomicConjugateMatterDerivativeDual current 0 direction +
        coframeRowCoordinateConjugateMatterResponse
          (current.coframe 0) response direction := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [installCoframeRowConjugateMatterResponse_coordinateDerivative_origin
    current conjugateDifferentiable response direction,
    matterDualOfCoordinates_add,
    matterDualOfCoordinates_surjective]
  rfl

theorem installCoframeRowConjugateMatterResponse_frameDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    holonomicFrameConjugateMatterDerivative
        (installCoframeRowConjugateMatterResponse current response) 0 =
      fun internal =>
        holonomicFrameConjugateMatterDerivative current 0 internal +
          frameTimeOnlyConjugateMatterResponse response internal := by
  unfold holonomicFrameConjugateMatterDerivative
  rw [installCoframeRowConjugateMatterResponse_coframe]
  rw [show
    holonomicConjugateMatterDerivativeDual
        (installCoframeRowConjugateMatterResponse current response) 0 =
      fun direction =>
        holonomicConjugateMatterDerivativeDual current 0 direction +
          coframeRowCoordinateConjugateMatterResponse
            (current.coframe 0) response direction by
    funext direction
    exact installCoframeRowConjugateMatterResponse_derivativeDual_origin
      current conjugateDifferentiable response direction]
  exact frameConjugateMatterDerivative_add_coframeRowResponse
    (current.coframe 0) nondegenerate
    (holonomicConjugateMatterDerivativeDual current 0) response

theorem installCoframeRowConjugateMatterResponse_frameTimeDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    holonomicFrameConjugateMatterDerivative
        (installCoframeRowConjugateMatterResponse current response) 0 0 =
      holonomicFrameConjugateMatterDerivative current 0 0 + response := by
  have effect := congrFun
    (installCoframeRowConjugateMatterResponse_frameDerivative_origin
      current conjugateDifferentiable nondegenerate response)
    (0 : LorentzianIndex)
  simpa [frameTimeOnlyConjugateMatterResponse] using effect

theorem installCoframeRowConjugateMatterResponse_frameSpatialDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (spatial : Fin 3) :
    holonomicFrameConjugateMatterDerivative
        (installCoframeRowConjugateMatterResponse current response)
        0 spatial.succ =
      holonomicFrameConjugateMatterDerivative current 0 spatial.succ := by
  have effect := congrFun
    (installCoframeRowConjugateMatterResponse_frameDerivative_origin
      current conjugateDifferentiable nondegenerate response) spatial.succ
  simpa [frameTimeOnlyConjugateMatterResponse] using effect

@[simp] theorem installCoframeRowConjugateMatterResponse_zero
    (current : StageNineHolonomicConfiguration) :
    installCoframeRowConjugateMatterResponse current 0 = current := by
  cases current
  simp [installCoframeRowConjugateMatterResponse,
    varyConjugateMatterCoordinates,
    coframeRowLinearConjugateMatterCoordinateWrite]

/-- The row installer has a faithful zero fiber at a nondegenerate origin. -/
theorem installCoframeRowConjugateMatterResponse_eq_iff
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    installCoframeRowConjugateMatterResponse current response = current ↔
      response = 0 := by
  constructor
  · intro actualEq
    have coordinateEq := congrArg
      (fun candidate : StageNineHolonomicConfiguration =>
        holonomicConjugateMatterCoordinates candidate
          (coframeNativeTemporalBaseDirection (current.coframe 0))) actualEq
    rw [installCoframeRowConjugateMatterResponse_coordinates] at coordinateEq
    have writeZero :
        coframeRowLinearConjugateMatterCoordinateWrite
            (current.coframe 0) response
            (coframeNativeTemporalBaseDirection (current.coframe 0)) = 0 := by
      exact add_left_cancel
        (show
          holonomicConjugateMatterCoordinates current
                (coframeNativeTemporalBaseDirection (current.coframe 0)) +
              coframeRowLinearConjugateMatterCoordinateWrite
                (current.coframe 0) response
                (coframeNativeTemporalBaseDirection (current.coframe 0)) =
            holonomicConjugateMatterCoordinates current
                (coframeNativeTemporalBaseDirection (current.coframe 0)) + 0 by
          simpa using coordinateEq)
    unfold coframeRowLinearConjugateMatterCoordinateWrite at writeZero
    rw [coframeRowLinearFunctional_nativeDirection
      (current.coframe 0) nondegenerate] at writeZero
    exact matterDualCoordinates_injective (by simpa using writeZero)
  · rintro rfl
    exact installCoframeRowConjugateMatterResponse_zero current

theorem installCoframeRowConjugateMatterResponse_nondegenerate
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installCoframeRowConjugateMatterResponse current response
      ).Nondegenerate := by
  simpa [StageNineHolonomicConfiguration.Nondegenerate] using nondegenerate

/-! ## Source/current-only frame-time action producer -/

def originFrameTimeConjugateMatterGeneratedDerivative
    (current : StageNineHolonomicConfiguration) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity current 0

def OriginFrameTimeConjugateMatterActionLaw
    (current : StageNineHolonomicConfiguration)
    (timeFrameDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    current 0 timeFrameDerivative

theorem originFrameTimeConjugateMatterGeneratedDerivative_satisfies_actionLaw
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    OriginFrameTimeConjugateMatterActionLaw current
      (originFrameTimeConjugateMatterGeneratedDerivative current) :=
  holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity_satisfies
    current 0 nondegenerate

theorem originFrameTimeConjugateMatterActionLaw_unique
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstLaw : OriginFrameTimeConjugateMatterActionLaw current first)
    (secondLaw : OriginFrameTimeConjugateMatterActionLaw current second) :
    first = second :=
  holonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw_unique
    current 0 nondegenerate first second firstLaw secondLaw

def originFrameTimeConjugateMatterResponse
    (current : StageNineHolonomicConfiguration) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  originFrameTimeConjugateMatterGeneratedDerivative current -
    holonomicFrameConjugateMatterDerivative current 0 0

def actionGeneratedOriginFrameTimeConjugateMatterActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installCoframeRowConjugateMatterResponse current
    (originFrameTimeConjugateMatterResponse current)

@[simp] theorem actionGeneratedOriginFrameTimeConjugateMatterActual_coframe
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current).coframe =
      current.coframe := rfl

@[simp] theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_gravityConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current
      ).gravityConnection = current.gravityConnection := rfl

@[simp] theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_gravityAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current
      ).gravityAuxiliary = current.gravityAuxiliary := rfl

@[simp] theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_gravitySimplicityMultiplier
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current
      ).gravitySimplicityMultiplier = current.gravitySimplicityMultiplier := rfl

@[simp] theorem actionGeneratedOriginFrameTimeConjugateMatterActual_gaugeConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current
      ).gaugeConnection = current.gaugeConnection := rfl

@[simp] theorem actionGeneratedOriginFrameTimeConjugateMatterActual_gaugeAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current
      ).gaugeAuxiliary = current.gaugeAuxiliary := rfl

@[simp] theorem actionGeneratedOriginFrameTimeConjugateMatterActual_scalar
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current).scalar =
      current.scalar := rfl

@[simp] theorem actionGeneratedOriginFrameTimeConjugateMatterActual_matter
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current).matter =
      current.matter := rfl

@[simp] theorem actionGeneratedOriginFrameTimeConjugateMatterActual_origin
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current
      ).conjugateMatter 0 = current.conjugateMatter 0 :=
  installCoframeRowConjugateMatterResponse_origin _ _

private theorem actionGeneratedOriginFrameTimeConjugateMatterActual_pointField_origin
    (current : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 =
      toContinuumPointField current 0 := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  exact actionGeneratedOriginFrameTimeConjugateMatterActual_origin current

private theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_drift_origin
    (current : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
        (actionGeneratedOriginFrameTimeConjugateMatterActual current)
        0 direction =
      holonomicLiveCoframeDensitizedPrincipalDriftCoordinates current
        0 direction := by
  unfold holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm holonomicConjugateMatterCoordinates
  rw [actionGeneratedOriginFrameTimeConjugateMatterActual_coframe,
    actionGeneratedOriginFrameTimeConjugateMatterActual_origin]

private theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_algebraicDual_origin
    (current : StageNineHolonomicConfiguration) :
    holonomicDiracDualLiveCoframeAlgebraicDual
        (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 =
      holonomicDiracDualLiveCoframeAlgebraicDual current 0 := by
  unfold holonomicDiracDualLiveCoframeAlgebraicDual
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [actionGeneratedOriginFrameTimeConjugateMatterActual_pointField_origin,
    actionGeneratedOriginFrameTimeConjugateMatterActual_origin,
    actionGeneratedOriginFrameTimeConjugateMatterActual_coframe,
    actionGeneratedOriginFrameTimeConjugateMatterActual_gravityConnection,
    actionGeneratedOriginFrameTimeConjugateMatterActual_gaugeConnection,
    actionGeneratedOriginFrameTimeConjugateMatterActual_scalar]

private theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_totalDrift_origin
    (current : StageNineHolonomicConfiguration) :
    holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
        (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 =
      holonomicLiveCoframeTotalDensitizedPrincipalDriftDual current 0 := by
  have spatialEq :
      holonomicLiveCoframeSpatialPrincipalDriftCoordinates
          (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 =
        holonomicLiveCoframeSpatialPrincipalDriftCoordinates current 0 := by
    unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
    apply Finset.sum_congr rfl
    intro direction _
    exact actionGeneratedOriginFrameTimeConjugateMatterActual_drift_origin
      current direction.succ
  have temporalEq :
      holonomicLiveCoframeTemporalPrincipalDriftCoordinates
          (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 =
        holonomicLiveCoframeTemporalPrincipalDriftCoordinates current 0 := by
    unfold holonomicLiveCoframeTemporalPrincipalDriftCoordinates
    exact actionGeneratedOriginFrameTimeConjugateMatterActual_drift_origin
      current canonicalLorentzianTimeDirection
  unfold holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
  rw [spatialEq, temporalEq]

theorem actionGeneratedOriginFrameTimeConjugateMatterActual_frameTimeDerivative
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    holonomicFrameConjugateMatterDerivative
        (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 0 =
      originFrameTimeConjugateMatterGeneratedDerivative current := by
  change
    holonomicFrameConjugateMatterDerivative
        (installCoframeRowConjugateMatterResponse current
          (originFrameTimeConjugateMatterResponse current)) 0 0 = _
  rw [installCoframeRowConjugateMatterResponse_frameTimeDerivative_origin
    current conjugateDifferentiable nondegenerate]
  unfold originFrameTimeConjugateMatterResponse
  abel

theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_frameSpatialDerivative
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (spatial : Fin 3) :
    holonomicFrameConjugateMatterDerivative
        (actionGeneratedOriginFrameTimeConjugateMatterActual current)
        0 spatial.succ =
      holonomicFrameConjugateMatterDerivative current 0 spatial.succ := by
  exact installCoframeRowConjugateMatterResponse_frameSpatialDerivative_origin
    current conjugateDifferentiable nondegenerate _ spatial

private theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_spatialPrincipalSum_origin
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    (∑ spatial : Fin 3,
        (holonomicFrameConjugateMatterDerivative
          (actionGeneratedOriginFrameTimeConjugateMatterActual current)
          0 spatial.succ).comp
            (identityCoframeMatterPrincipal spatial.succ)) =
      ∑ spatial : Fin 3,
        (holonomicFrameConjugateMatterDerivative current 0 spatial.succ).comp
          (identityCoframeMatterPrincipal spatial.succ) := by
  apply Finset.sum_congr rfl
  intro spatial _
  rw [actionGeneratedOriginFrameTimeConjugateMatterActual_frameSpatialDerivative
    current conjugateDifferentiable nondegenerate spatial]

/-- The complete action-known frame dual is unchanged by the time-slot
write. -/
theorem actionGeneratedOriginFrameTimeConjugateMatterActual_knownDual
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
        (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 =
      holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
        current 0 := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
  rw [actionGeneratedOriginFrameTimeConjugateMatterActual_algebraicDual_origin,
    actionGeneratedOriginFrameTimeConjugateMatterActual_pointField_origin,
    actionGeneratedOriginFrameTimeConjugateMatterActual_spatialPrincipalSum_origin
      current conjugateDifferentiable nondegenerate,
    actionGeneratedOriginFrameTimeConjugateMatterActual_totalDrift_origin]

/-- Re-substitution of the generated time derivative into the complete
frame-adjoint action law on the same output actual. -/
theorem actionGeneratedOriginFrameTimeConjugateMatterActual_satisfies_actionLaw
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0
      (holonomicFrameConjugateMatterDerivative
        (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 0) := by
  have generatedLaw :=
    originFrameTimeConjugateMatterGeneratedDerivative_satisfies_actionLaw
      current nondegenerate
  unfold OriginFrameTimeConjugateMatterActionLaw at generatedLaw
  unfold HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    at generatedLaw ⊢
  rw [actionGeneratedOriginFrameTimeConjugateMatterActual_pointField_origin,
    actionGeneratedOriginFrameTimeConjugateMatterActual_knownDual
      current conjugateDifferentiable nondegenerate,
    actionGeneratedOriginFrameTimeConjugateMatterActual_frameTimeDerivative
      current conjugateDifferentiable nondegenerate]
  exact generatedLaw

/-- Compatibility name for consumers that expose the exact differentiability
mouth explicitly. -/
theorem
    actionGeneratedOriginFrameTimeConjugateMatterActual_satisfies_actionLaw_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0
      (holonomicFrameConjugateMatterDerivative
        (actionGeneratedOriginFrameTimeConjugateMatterActual current) 0 0) :=
  actionGeneratedOriginFrameTimeConjugateMatterActual_satisfies_actionLaw
    current conjugateDifferentiable nondegenerate

theorem originFrameTimeConjugateMatterResponse_unique
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (candidateLaw :
      OriginFrameTimeConjugateMatterActionLaw current
        (holonomicFrameConjugateMatterDerivative current 0 0 + candidate)) :
    candidate = originFrameTimeConjugateMatterResponse current := by
  have derivativeEq := originFrameTimeConjugateMatterActionLaw_unique
    current nondegenerate
    (holonomicFrameConjugateMatterDerivative current 0 0 + candidate)
    (originFrameTimeConjugateMatterGeneratedDerivative current)
    candidateLaw
    (originFrameTimeConjugateMatterGeneratedDerivative_satisfies_actionLaw
      current nondegenerate)
  unfold originFrameTimeConjugateMatterResponse
  apply eq_sub_of_add_eq
  calc
    candidate + holonomicFrameConjugateMatterDerivative current 0 0 =
        holonomicFrameConjugateMatterDerivative current 0 0 + candidate :=
      add_comm _ _
    _ = originFrameTimeConjugateMatterGeneratedDerivative current :=
      derivativeEq

theorem actionGeneratedOriginFrameTimeConjugateMatterActual_eq_iff
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    actionGeneratedOriginFrameTimeConjugateMatterActual current = current ↔
      originFrameTimeConjugateMatterResponse current = 0 :=
  installCoframeRowConjugateMatterResponse_eq_iff current nondegenerate _

theorem actionGeneratedOriginFrameTimeConjugateMatterActual_nondegenerate
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (actionGeneratedOriginFrameTimeConjugateMatterActual current
      ).Nondegenerate :=
  installCoframeRowConjugateMatterResponse_nondegenerate current
    nondegenerate _

/-! ## Ordered primal--adjoint occurrence -/

/-- The primal mother-action write followed by the adjoint frame-action
write on that exact post-primal actual. -/
def actionGeneratedOriginPrimalAdjointActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  actionGeneratedOriginFrameTimeConjugateMatterActual
    (actionGeneratedOriginFrameTimeMatterActual current)

theorem actionGeneratedOriginPrimalAdjointActual_satisfies_primalActionLaw_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    FrameTimeMatterActionLaw
      ((actionGeneratedOriginPrimalAdjointActual current).coframe 0)
      (holonomicMatterCovariantDerivative
        (actionGeneratedOriginPrimalAdjointActual current) 0)
      (scalarCoordinateEquiv.symm
        ((actionGeneratedOriginPrimalAdjointActual current).scalar 0))
      ((actionGeneratedOriginPrimalAdjointActual current).matter 0)
      (frameMatterDerivative
        ((actionGeneratedOriginPrimalAdjointActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedOriginPrimalAdjointActual current) 0) 0) := by
  unfold actionGeneratedOriginPrimalAdjointActual
    actionGeneratedOriginFrameTimeConjugateMatterActual
  rw [holonomicMatterCovariantDerivative_installCoframeRowConjugateMatterResponse]
  simpa using
    actionGeneratedOriginFrameTimeMatterActual_satisfies_actionLaw_of_differentiable
      current matterDifferentiable nondegenerate

theorem actionGeneratedOriginPrimalAdjointActual_satisfies_adjointActionLaw_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (conjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      (actionGeneratedOriginPrimalAdjointActual current) 0
      (holonomicFrameConjugateMatterDerivative
        (actionGeneratedOriginPrimalAdjointActual current) 0 0) := by
  unfold actionGeneratedOriginPrimalAdjointActual
  apply
    actionGeneratedOriginFrameTimeConjugateMatterActual_satisfies_actionLaw_of_differentiable
  · change DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current) 0
    exact conjugateDifferentiable
  · simpa using nondegenerate

theorem actionGeneratedOriginPrimalAdjointActual_satisfies_primalActionLaw
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    FrameTimeMatterActionLaw
      ((actionGeneratedOriginPrimalAdjointActual current).coframe 0)
      (holonomicMatterCovariantDerivative
        (actionGeneratedOriginPrimalAdjointActual current) 0)
      (scalarCoordinateEquiv.symm
        ((actionGeneratedOriginPrimalAdjointActual current).scalar 0))
      ((actionGeneratedOriginPrimalAdjointActual current).matter 0)
      (frameMatterDerivative
        ((actionGeneratedOriginPrimalAdjointActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedOriginPrimalAdjointActual current) 0) 0) :=
  actionGeneratedOriginPrimalAdjointActual_satisfies_primalActionLaw_of_differentiable
    current
    ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
    nondegenerate

theorem actionGeneratedOriginPrimalAdjointActual_satisfies_adjointActionLaw
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      (actionGeneratedOriginPrimalAdjointActual current) 0
      (holonomicFrameConjugateMatterDerivative
        (actionGeneratedOriginPrimalAdjointActual current) 0 0) :=
  actionGeneratedOriginPrimalAdjointActual_satisfies_adjointActionLaw_of_differentiable
    current
    ((holonomicConjugateMatterCoordinates_contDiff current smooth
      ).differentiable (by simp) |>.differentiableAt)
    nondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeConjugateMatterOriginActionWrite
