import H0mework.Physics.Coframe.CoframeNativeMatterFrameAction
import H0mework.Physics.Coframe.CurrentCoframeMatterTimeResponseActualLift

/-!
# Coframe-native primal matter origin action write

The current coframe generates a linear coordinate write along its own `e⁰`
row.  Its frame projection changes only `D_{E₀}ψ`, so the existing
frame-time mother-action solve installs without reading a residual or target.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterOriginActionWrite

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeMatterFrameAction
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286ActionVelocityLocalActualLift
open SU7ExteriorBreakingYukawa
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The current-owned linear functional `p ↦ e⁰(p)`. -/
def coframeRowLinearFunctional
    (coframe : LorentzianCoframe) : BasePoint →L[ℝ] ℝ :=
  ∑ coordinate : LorentzianIndex,
    (coframe 0 coordinate) • localBaseCoordinate coordinate

@[simp] theorem coframeRowLinearFunctional_apply
    (coframe : LorentzianCoframe)
    (point : BasePoint) :
    coframeRowLinearFunctional coframe point =
      ∑ coordinate : LorentzianIndex,
        coframe 0 coordinate * point coordinate := by
  simp [coframeRowLinearFunctional, localBaseCoordinate_apply]

theorem coframeRowLinearFunctional_coordinateDirection
    (coframe : LorentzianCoframe)
    (direction : LorentzianIndex) :
    coframeRowLinearFunctional coframe (coordinateDirection direction) =
      coframe 0 direction := by
  simp [coframeRowLinearFunctional_apply, coordinateDirection]

def coframeNativeTemporalBaseDirection
    (coframe : LorentzianCoframe) : BasePoint :=
  WithLp.toLp 2 fun coordinate =>
    coframeNativeTemporalDirection coframe coordinate

theorem coframeRowLinearFunctional_nativeDirection
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeRowLinearFunctional coframe
        (coframeNativeTemporalBaseDirection coframe) = 1 := by
  simpa [coframeRowLinearFunctional_apply,
    coframeNativeTemporalBaseDirection,
    coframeNativeTemporalCovector] using
    coframeNativeTemporal_pairing coframe nondegenerate

/-- Linear coordinate write whose derivative is
`δD_μψ = e⁰_μ r`. -/
def coframeRowLinearMatterCoordinateWrite
    (coframe : LorentzianCoframe)
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  coframeRowLinearFunctional coframe point • matterCoordinateEquiv response

@[simp] theorem coframeRowLinearMatterCoordinateWrite_origin
    (coframe : LorentzianCoframe)
    (response : DiracExteriorMatterCarrier) :
    coframeRowLinearMatterCoordinateWrite coframe response 0 = 0 := by
  simp [coframeRowLinearMatterCoordinateWrite]

theorem coframeRowLinearMatterCoordinateWrite_directionalDerivative
    (coframe : LorentzianCoframe)
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (coframeRowLinearMatterCoordinateWrite coframe response)
        point direction =
      matterCoordinateEquiv
        ((coframe 0 direction : ℂ) • response) := by
  have derivative :=
    (coframeRowLinearFunctional coframe).hasFDerivAt (x := point)
      |>.smul_const (matterCoordinateEquiv response)
  unfold fieldDirectionalDerivative coframeRowLinearMatterCoordinateWrite
  rw [derivative.fderiv]
  change
    coframeRowLinearFunctional coframe (coordinateDirection direction) •
        matterCoordinateEquiv response =
      matterCoordinateEquiv ((coframe 0 direction : ℂ) • response)
  rw [coframeRowLinearFunctional_coordinateDirection]
  rw [map_smul]
  rfl

theorem coframeRowLinearMatterCoordinateWrite_contDiff
    (coframe : LorentzianCoframe)
    (response : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (coframeRowLinearMatterCoordinateWrite coframe response) :=
  (coframeRowLinearFunctional coframe).contDiff.smul contDiff_const

/-- A response occupying only the internal frame-time slot. -/
def frameTimeOnlyMatterResponse
    (response : DiracExteriorMatterCarrier) : MatterDerivativeFamily :=
  fun internal => if internal = 0 then response else 0

/-- Its coordinate expression is the coframe row `e⁰_μ r`. -/
def coframeRowCoordinateMatterResponse
    (coframe : LorentzianCoframe)
    (response : DiracExteriorMatterCarrier) : MatterDerivativeFamily :=
  fun coordinate => (coframe 0 coordinate : ℂ) • response

theorem coordinateMatterDerivative_frameTimeOnly
    (coframe : LorentzianCoframe)
    (response : DiracExteriorMatterCarrier) :
    coordinateMatterDerivative coframe
        (frameTimeOnlyMatterResponse response) =
      coframeRowCoordinateMatterResponse coframe response := by
  funext coordinate
  unfold coordinateMatterDerivative frameTimeOnlyMatterResponse
    coframeRowCoordinateMatterResponse
  rw [Finset.sum_eq_single (0 : LorentzianIndex)]
  · simp
  · intro candidate _ candidateNe
    simp [candidateNe]
  · simp

theorem frameMatterDerivative_coframeRowCoordinateMatterResponse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    frameMatterDerivative coframe
        (coframeRowCoordinateMatterResponse coframe response) =
      frameTimeOnlyMatterResponse response := by
  rw [← coordinateMatterDerivative_frameTimeOnly]
  exact frameMatterDerivative_coordinateMatterDerivative
    coframe nondegenerate (frameTimeOnlyMatterResponse response)

theorem frameMatterDerivative_add_coframeRowResponse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coordinateDerivative : MatterDerivativeFamily)
    (response : DiracExteriorMatterCarrier) :
    frameMatterDerivative coframe
        (fun coordinate =>
          coordinateDerivative coordinate +
            coframeRowCoordinateMatterResponse coframe response coordinate) =
      fun internal =>
        frameMatterDerivative coframe coordinateDerivative internal +
          frameTimeOnlyMatterResponse response internal := by
  funext internal
  unfold frameMatterDerivative
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  exact congrFun
    (frameMatterDerivative_coframeRowCoordinateMatterResponse
      coframe nondegenerate response) internal

/-- Install a generated frame-time response while retaining every other
primitive field. -/
def installCoframeRowMatterResponse
    (current : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  varyMatterCoordinates current
    (coframeRowLinearMatterCoordinateWrite (current.coframe 0) response) 1

@[simp] theorem installCoframeRowMatterResponse_coframe
    (current : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installCoframeRowMatterResponse current response).coframe =
      current.coframe := rfl

@[simp] theorem installCoframeRowMatterResponse_gravityConnection
    (current : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installCoframeRowMatterResponse current response).gravityConnection =
      current.gravityConnection := rfl

@[simp] theorem installCoframeRowMatterResponse_gaugeConnection
    (current : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installCoframeRowMatterResponse current response).gaugeConnection =
      current.gaugeConnection := rfl

@[simp] theorem installCoframeRowMatterResponse_scalar
    (current : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installCoframeRowMatterResponse current response).scalar =
      current.scalar := rfl

theorem installCoframeRowMatterResponse_matter_coordinate
    (current : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterCoordinateEquiv
        ((installCoframeRowMatterResponse current response).matter point) =
      matterCoordinateEquiv (current.matter point) +
        coframeRowLinearMatterCoordinateWrite
          (current.coframe 0) response point := by
  simp [installCoframeRowMatterResponse, varyMatterCoordinates]

@[simp] theorem installCoframeRowMatterResponse_matter_origin
    (current : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installCoframeRowMatterResponse current response).matter 0 =
      current.matter 0 := by
  apply matterCoordinateEquiv.injective
  simp [installCoframeRowMatterResponse_matter_coordinate]

private theorem installCoframeRowMatterResponse_matterCoordinateDerivative_origin_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((installCoframeRowMatterResponse current response).matter point))
        0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (current.matter point))
          0 direction +
        matterCoordinateEquiv
          ((current.coframe 0 0 direction : ℂ) • response) := by
  have responseDifferentiable : DifferentiableAt ℝ
      (coframeRowLinearMatterCoordinateWrite
        (current.coframe 0) response) 0 :=
    (coframeRowLinearMatterCoordinateWrite_contDiff
      (current.coframe 0) response).differentiable (by simp)
      |>.differentiableAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point =>
      matterCoordinateEquiv
        ((installCoframeRowMatterResponse current response).matter point)) =
      (fun point => matterCoordinateEquiv (current.matter point)) +
        coframeRowLinearMatterCoordinateWrite
          (current.coframe 0) response by
    funext point
    exact installCoframeRowMatterResponse_matter_coordinate
      current response point]
  rw [fderiv_add matterDifferentiable responseDifferentiable, add_apply]
  change
    _ + fieldDirectionalDerivative
          (coframeRowLinearMatterCoordinateWrite
            (current.coframe 0) response) 0 direction = _
  rw [coframeRowLinearMatterCoordinateWrite_directionalDerivative]

theorem installCoframeRowMatterResponse_matterCoordinateDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((installCoframeRowMatterResponse current response).matter point))
        0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (current.matter point))
          0 direction +
        matterCoordinateEquiv
          ((current.coframe 0 0 direction : ℂ) • response) := by
  exact
    installCoframeRowMatterResponse_matterCoordinateDerivative_origin_of_differentiable
      current
      ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
      response direction

private theorem holonomicMatterCovariantDerivative_installCoframeRowMatterResponse_origin_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (installCoframeRowMatterResponse current response) 0 direction =
      holonomicMatterCovariantDerivative current 0 direction +
        coframeRowCoordinateMatterResponse
          (current.coframe 0) response direction := by
  unfold holonomicMatterCovariantDerivative
  rw [installCoframeRowMatterResponse_matterCoordinateDerivative_origin_of_differentiable
    current matterDifferentiable response direction]
  simp only [map_add, matterCoordinateEquiv.symm_apply_apply,
    installCoframeRowMatterResponse_gravityConnection,
    installCoframeRowMatterResponse_gaugeConnection,
    installCoframeRowMatterResponse_matter_origin]
  unfold coframeRowCoordinateMatterResponse
  module

theorem holonomicMatterCovariantDerivative_installCoframeRowMatterResponse_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (installCoframeRowMatterResponse current response) 0 direction =
      holonomicMatterCovariantDerivative current 0 direction +
        coframeRowCoordinateMatterResponse
          (current.coframe 0) response direction := by
  exact
    holonomicMatterCovariantDerivative_installCoframeRowMatterResponse_origin_of_differentiable
      current
      ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
      response direction

@[simp] theorem installCoframeRowMatterResponse_zero
    (current : StageNineHolonomicConfiguration) :
    installCoframeRowMatterResponse current 0 = current := by
  cases current
  simp [installCoframeRowMatterResponse, varyMatterCoordinates,
    coframeRowLinearMatterCoordinateWrite]

theorem installCoframeRowMatterResponse_eq_iff
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    installCoframeRowMatterResponse current response = current ↔
      response = 0 := by
  constructor
  · intro actualEq
    have matterEq := congrArg
      (fun candidate : StageNineHolonomicConfiguration =>
        matterCoordinateEquiv
          (candidate.matter
            (coframeNativeTemporalBaseDirection (current.coframe 0))))
      actualEq
    rw [installCoframeRowMatterResponse_matter_coordinate] at matterEq
    have writeZero :
        coframeRowLinearMatterCoordinateWrite (current.coframe 0) response
            (coframeNativeTemporalBaseDirection (current.coframe 0)) = 0 := by
      exact add_left_cancel
        (show
          matterCoordinateEquiv
                (current.matter
                  (coframeNativeTemporalBaseDirection (current.coframe 0))) +
              coframeRowLinearMatterCoordinateWrite (current.coframe 0)
                response
                (coframeNativeTemporalBaseDirection (current.coframe 0)) =
            matterCoordinateEquiv
                (current.matter
                  (coframeNativeTemporalBaseDirection (current.coframe 0))) +
              0 by simpa using matterEq)
    unfold coframeRowLinearMatterCoordinateWrite at writeZero
    rw [coframeRowLinearFunctional_nativeDirection
      (current.coframe 0) nondegenerate] at writeZero
    apply matterCoordinateEquiv.injective
    simpa using writeZero
  · rintro rfl
    exact installCoframeRowMatterResponse_zero current

private theorem installCoframeRowMatterResponse_frameDerivative_origin_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0) =
      fun internal =>
        frameMatterDerivative (current.coframe 0)
            (holonomicMatterCovariantDerivative current 0) internal +
          frameTimeOnlyMatterResponse response internal := by
  rw [show
    holonomicMatterCovariantDerivative
        (installCoframeRowMatterResponse current response) 0 =
      fun direction =>
        holonomicMatterCovariantDerivative current 0 direction +
          coframeRowCoordinateMatterResponse
            (current.coframe 0) response direction by
    funext direction
    exact
      holonomicMatterCovariantDerivative_installCoframeRowMatterResponse_origin_of_differentiable
        current matterDifferentiable response direction]
  exact frameMatterDerivative_add_coframeRowResponse
    (current.coframe 0) nondegenerate
    (holonomicMatterCovariantDerivative current 0) response

private theorem installCoframeRowMatterResponse_frameTimeDerivative_origin_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0) 0 =
      frameMatterDerivative (current.coframe 0)
          (holonomicMatterCovariantDerivative current 0) 0 + response := by
  have effect := congrFun
    (installCoframeRowMatterResponse_frameDerivative_origin_of_differentiable
      current matterDifferentiable nondegenerate response)
    (0 : LorentzianIndex)
  simpa [frameTimeOnlyMatterResponse] using effect

private theorem installCoframeRowMatterResponse_frameSpatialDerivative_origin_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier)
    (spatial : Fin 3) :
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0)
        spatial.succ =
      frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative current 0) spatial.succ := by
  have effect := congrFun
    (installCoframeRowMatterResponse_frameDerivative_origin_of_differentiable
      current matterDifferentiable nondegenerate response) spatial.succ
  simpa [frameTimeOnlyMatterResponse] using effect

private theorem installCoframeRowMatterResponse_frameTimeKnownVector_origin_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    frameTimeMatterKnownVector (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0)
        (scalarCoordinateEquiv.symm (current.scalar 0))
        (current.matter 0) =
      frameTimeMatterKnownVector (current.coframe 0)
        (holonomicMatterCovariantDerivative current 0)
        (scalarCoordinateEquiv.symm (current.scalar 0))
        (current.matter 0) := by
  unfold frameTimeMatterKnownVector
  simp_rw [installCoframeRowMatterResponse_frameSpatialDerivative_origin_of_differentiable
    current matterDifferentiable nondegenerate response]

theorem installCoframeRowMatterResponse_frameDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0) =
      fun internal =>
        frameMatterDerivative (current.coframe 0)
            (holonomicMatterCovariantDerivative current 0) internal +
          frameTimeOnlyMatterResponse response internal :=
  installCoframeRowMatterResponse_frameDerivative_origin_of_differentiable
    current
    ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
    nondegenerate response

theorem installCoframeRowMatterResponse_frameTimeDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0) 0 =
      frameMatterDerivative (current.coframe 0)
          (holonomicMatterCovariantDerivative current 0) 0 + response :=
  installCoframeRowMatterResponse_frameTimeDerivative_origin_of_differentiable
    current
    ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
    nondegenerate response

theorem installCoframeRowMatterResponse_frameSpatialDerivative_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier)
    (spatial : Fin 3) :
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0)
        spatial.succ =
      frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative current 0) spatial.succ :=
  installCoframeRowMatterResponse_frameSpatialDerivative_origin_of_differentiable
    current
    ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
    nondegenerate response spatial

theorem installCoframeRowMatterResponse_frameTimeKnownVector_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (response : DiracExteriorMatterCarrier) :
    frameTimeMatterKnownVector (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current response) 0)
        (scalarCoordinateEquiv.symm (current.scalar 0))
        (current.matter 0) =
      frameTimeMatterKnownVector (current.coframe 0)
        (holonomicMatterCovariantDerivative current 0)
        (scalarCoordinateEquiv.symm (current.scalar 0))
        (current.matter 0) :=
  installCoframeRowMatterResponse_frameTimeKnownVector_origin_of_differentiable
    current
    ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
    nondegenerate response

/-! ## Source/current-only generated origin actual -/

def originFrameTimeMatterGeneratedDerivative
    (current : StageNineHolonomicConfiguration) :
    DiracExteriorMatterCarrier :=
  actionGeneratedFrameTimeMatterDerivative
    (current.coframe 0)
    (holonomicMatterCovariantDerivative current 0)
    (scalarCoordinateEquiv.symm (current.scalar 0))
    (current.matter 0)

def OriginFrameTimeMatterActionLaw
    (current : StageNineHolonomicConfiguration)
    (timeFrameDerivative : DiracExteriorMatterCarrier) : Prop :=
  FrameTimeMatterActionLaw (current.coframe 0)
    (holonomicMatterCovariantDerivative current 0)
    (scalarCoordinateEquiv.symm (current.scalar 0))
    (current.matter 0) timeFrameDerivative

theorem originFrameTimeMatterGeneratedDerivative_satisfies_actionLaw
    (current : StageNineHolonomicConfiguration) :
    OriginFrameTimeMatterActionLaw current
      (originFrameTimeMatterGeneratedDerivative current) :=
  actionGeneratedFrameTimeMatterDerivative_satisfies_actionLaw
    (current.coframe 0)
    (holonomicMatterCovariantDerivative current 0)
    (scalarCoordinateEquiv.symm (current.scalar 0))
    (current.matter 0)

theorem originFrameTimeMatterActionLaw_unique
    (current : StageNineHolonomicConfiguration)
    (first second : DiracExteriorMatterCarrier)
    (firstLaw : OriginFrameTimeMatterActionLaw current first)
    (secondLaw : OriginFrameTimeMatterActionLaw current second) :
    first = second :=
  frameTimeMatterActionLaw_unique
    (current.coframe 0)
    (holonomicMatterCovariantDerivative current 0)
    (scalarCoordinateEquiv.symm (current.scalar 0))
    (current.matter 0) first second firstLaw secondLaw

def originFrameTimeMatterResponse
    (current : StageNineHolonomicConfiguration) :
    DiracExteriorMatterCarrier :=
  originFrameTimeMatterGeneratedDerivative current -
    frameMatterDerivative (current.coframe 0)
      (holonomicMatterCovariantDerivative current 0) 0

def actionGeneratedOriginFrameTimeMatterActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installCoframeRowMatterResponse current
    (originFrameTimeMatterResponse current)

@[simp] theorem actionGeneratedOriginFrameTimeMatterActual_coframe
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeMatterActual current).coframe =
      current.coframe := rfl

@[simp] theorem actionGeneratedOriginFrameTimeMatterActual_gravityConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeMatterActual current).gravityConnection =
      current.gravityConnection := rfl

@[simp] theorem actionGeneratedOriginFrameTimeMatterActual_gaugeConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeMatterActual current).gaugeConnection =
      current.gaugeConnection := rfl

@[simp] theorem actionGeneratedOriginFrameTimeMatterActual_scalar
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeMatterActual current).scalar =
      current.scalar := rfl

@[simp] theorem actionGeneratedOriginFrameTimeMatterActual_matter_origin
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedOriginFrameTimeMatterActual current).matter 0 =
      current.matter 0 :=
  installCoframeRowMatterResponse_matter_origin _ _

theorem actionGeneratedOriginFrameTimeMatterActual_frameTimeDerivative
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    frameMatterDerivative
        ((actionGeneratedOriginFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedOriginFrameTimeMatterActual current) 0) 0 =
      originFrameTimeMatterGeneratedDerivative current := by
  change
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current
            (originFrameTimeMatterResponse current)) 0) 0 = _
  rw [installCoframeRowMatterResponse_frameTimeDerivative_origin
    current smooth nondegenerate]
  unfold originFrameTimeMatterResponse
  abel

theorem actionGeneratedOriginFrameTimeMatterActual_frameSpatialDerivative
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (spatial : Fin 3) :
    frameMatterDerivative
        ((actionGeneratedOriginFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedOriginFrameTimeMatterActual current) 0)
        spatial.succ =
      frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative current 0) spatial.succ := by
  change
    frameMatterDerivative (current.coframe 0)
        (holonomicMatterCovariantDerivative
          (installCoframeRowMatterResponse current
            (originFrameTimeMatterResponse current)) 0) spatial.succ = _
  exact installCoframeRowMatterResponse_frameSpatialDerivative_origin
    current smooth nondegenerate _ spatial

theorem actionGeneratedOriginFrameTimeMatterActual_knownVector
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    frameTimeMatterKnownVector
        ((actionGeneratedOriginFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedOriginFrameTimeMatterActual current) 0)
        (scalarCoordinateEquiv.symm
          ((actionGeneratedOriginFrameTimeMatterActual current).scalar 0))
        ((actionGeneratedOriginFrameTimeMatterActual current).matter 0) =
      frameTimeMatterKnownVector (current.coframe 0)
        (holonomicMatterCovariantDerivative current 0)
        (scalarCoordinateEquiv.symm (current.scalar 0))
        (current.matter 0) := by
  rw [actionGeneratedOriginFrameTimeMatterActual_coframe,
    actionGeneratedOriginFrameTimeMatterActual_scalar,
    actionGeneratedOriginFrameTimeMatterActual_matter_origin]
  unfold actionGeneratedOriginFrameTimeMatterActual
  exact installCoframeRowMatterResponse_frameTimeKnownVector_origin
    current smooth nondegenerate _

/-- The origin write needs only the exact local first jet that it changes;
global smoothness is a convenience wrapper, not part of the producer mouth. -/
theorem actionGeneratedOriginFrameTimeMatterActual_satisfies_actionLaw_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (matterDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    FrameTimeMatterActionLaw
      ((actionGeneratedOriginFrameTimeMatterActual current).coframe 0)
      (holonomicMatterCovariantDerivative
        (actionGeneratedOriginFrameTimeMatterActual current) 0)
      (scalarCoordinateEquiv.symm
        ((actionGeneratedOriginFrameTimeMatterActual current).scalar 0))
      ((actionGeneratedOriginFrameTimeMatterActual current).matter 0)
      (frameMatterDerivative
        ((actionGeneratedOriginFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedOriginFrameTimeMatterActual current) 0) 0) := by
  have generatedLaw :=
    actionGeneratedFrameTimeMatterDerivative_satisfies_actionLaw
      (current.coframe 0)
      (holonomicMatterCovariantDerivative current 0)
      (scalarCoordinateEquiv.symm (current.scalar 0))
      (current.matter 0)
  unfold FrameTimeMatterActionLaw at generatedLaw ⊢
  rw [actionGeneratedOriginFrameTimeMatterActual_coframe,
    actionGeneratedOriginFrameTimeMatterActual_scalar,
    actionGeneratedOriginFrameTimeMatterActual_matter_origin]
  unfold actionGeneratedOriginFrameTimeMatterActual
  rw [installCoframeRowMatterResponse_frameTimeKnownVector_origin_of_differentiable
      current matterDifferentiable nondegenerate
      (originFrameTimeMatterResponse current),
    installCoframeRowMatterResponse_frameTimeDerivative_origin_of_differentiable
      current matterDifferentiable nondegenerate
      (originFrameTimeMatterResponse current)]
  unfold originFrameTimeMatterResponse originFrameTimeMatterGeneratedDerivative
  rw [add_sub_cancel]
  exact generatedLaw

/-- Re-substitution into the same mother-action equation on the same origin
actual. -/
theorem actionGeneratedOriginFrameTimeMatterActual_satisfies_actionLaw
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    FrameTimeMatterActionLaw
      ((actionGeneratedOriginFrameTimeMatterActual current).coframe 0)
      (holonomicMatterCovariantDerivative
        (actionGeneratedOriginFrameTimeMatterActual current) 0)
      (scalarCoordinateEquiv.symm
        ((actionGeneratedOriginFrameTimeMatterActual current).scalar 0))
      ((actionGeneratedOriginFrameTimeMatterActual current).matter 0)
      (frameMatterDerivative
        ((actionGeneratedOriginFrameTimeMatterActual current).coframe 0)
        (holonomicMatterCovariantDerivative
          (actionGeneratedOriginFrameTimeMatterActual current) 0) 0) :=
  actionGeneratedOriginFrameTimeMatterActual_satisfies_actionLaw_of_differentiable
    current
    ((smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt)
    nondegenerate

/-- Any response whose resulting frame-time derivative satisfies the same
origin action law is the generated response.  The installer projection
theorem above identifies its derivative with this exact `old + candidate`
mouth. -/
theorem originFrameTimeMatterResponse_unique
    (current : StageNineHolonomicConfiguration)
    (candidate : DiracExteriorMatterCarrier)
    (candidateLaw :
      OriginFrameTimeMatterActionLaw current
        (frameMatterDerivative (current.coframe 0)
            (holonomicMatterCovariantDerivative current 0) 0 + candidate)) :
    candidate = originFrameTimeMatterResponse current := by
  have derivativeEq := originFrameTimeMatterActionLaw_unique current
    (frameMatterDerivative (current.coframe 0)
      (holonomicMatterCovariantDerivative current 0) 0 + candidate)
    (originFrameTimeMatterGeneratedDerivative current)
    candidateLaw
    (originFrameTimeMatterGeneratedDerivative_satisfies_actionLaw current)
  unfold originFrameTimeMatterResponse
  apply eq_sub_of_add_eq
  calc
    candidate +
          frameMatterDerivative (current.coframe 0)
            (holonomicMatterCovariantDerivative current 0) 0 =
        frameMatterDerivative (current.coframe 0)
            (holonomicMatterCovariantDerivative current 0) 0 + candidate :=
      add_comm _ _
    _ = originFrameTimeMatterGeneratedDerivative current := derivativeEq

theorem actionGeneratedOriginFrameTimeMatterActual_eq_iff
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0) :
    actionGeneratedOriginFrameTimeMatterActual current = current ↔
      originFrameTimeMatterResponse current = 0 := by
  exact installCoframeRowMatterResponse_eq_iff current nondegenerate _

end

end SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterOriginActionWrite
