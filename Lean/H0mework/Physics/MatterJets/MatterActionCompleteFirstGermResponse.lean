import H0mework.Physics.MatterJets.MatterCompleteFirstGermPrincipal

/-!
# S9-C3h183a: complete primal-matter first-germ response

This module realizes the C3h183a principal response as a canonical quadratic
matter-coordinate correction and installs it on an already generated actual.
The complete action residual is read internally; callers supply no residual,
jet, branch, or acceptance certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineMatterActionCompleteFirstGermResponse

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterCompleteFirstGermPrincipal
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineScalarActionSecondJetLocalActualLift
open SU7ExteriorBreakingYukawa
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-! ## Canonical temporal-pivot quadratic correction -/

/-- The mixed time--space monomial.  Its normalization is fixed by the
Hessian readback: unlike the time--time monomial, it carries no factor `1/2`.
-/
def matterMixedTimeSpatialCoefficient
    (axis : Fin 3) (point : BasePoint) : ℝ :=
  localBaseCoordinate canonicalLorentzianTimeDirection point *
    localBaseCoordinate axis.succ point

/-- One mixed time--space matter-coordinate correction. -/
def matterMixedTimeSpatialCoordinateCorrection
    (axis : Fin 3)
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterMixedTimeSpatialCoefficient axis point •
    matterCoordinateEquiv response

/-- The unique quadratic correction represented by the temporal-pivot
Hessian.  It contains no spatial--spatial monomial, so it preserves the full
initial `t = 0` slice. -/
def matterCompleteQuadraticCoordinateCorrection
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterQuadraticTimeCoordinateCorrection hessian.timeTime point +
    ∑ axis : Fin 3,
      matterMixedTimeSpatialCoordinateCorrection axis
        (hessian.timeSpatial axis) point

@[simp] theorem matterMixedTimeSpatialCoefficient_origin
    (axis : Fin 3) :
    matterMixedTimeSpatialCoefficient axis 0 = 0 := by
  simp [matterMixedTimeSpatialCoefficient]

theorem matterMixedTimeSpatialCoefficient_eq_zero_of_time_zero
    (axis : Fin 3) (point : BasePoint)
    (timeZero : point canonicalLorentzianTimeDirection = 0) :
    matterMixedTimeSpatialCoefficient axis point = 0 := by
  simp [matterMixedTimeSpatialCoefficient, localBaseCoordinate, timeZero]

@[simp] theorem matterMixedTimeSpatialCoordinateCorrection_origin
    (axis : Fin 3) (response : DiracExteriorMatterCarrier) :
    matterMixedTimeSpatialCoordinateCorrection axis response 0 = 0 := by
  simp [matterMixedTimeSpatialCoordinateCorrection]

theorem matterMixedTimeSpatialCoordinateCorrection_eq_zero_of_time_zero
    (axis : Fin 3) (response : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (timeZero : point canonicalLorentzianTimeDirection = 0) :
    matterMixedTimeSpatialCoordinateCorrection axis response point = 0 := by
  simp [matterMixedTimeSpatialCoordinateCorrection,
    matterMixedTimeSpatialCoefficient_eq_zero_of_time_zero axis point timeZero]

theorem matterMixedTimeSpatialCoordinateCorrection_directionalDerivative
    (axis : Fin 3)
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterMixedTimeSpatialCoordinateCorrection axis response)
        point direction =
      ((coordinateDirection direction canonicalLorentzianTimeDirection) *
          point axis.succ +
        point canonicalLorentzianTimeDirection *
          coordinateDirection direction axis.succ) •
        matterCoordinateEquiv response := by
  have coefficientDerivative :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := point) |>.mul
        ((localBaseCoordinate axis.succ).hasFDerivAt (x := point))
  have correctionDerivative :=
    coefficientDerivative.smul_const (matterCoordinateEquiv response)
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ
      (fun candidate =>
        ((⇑(localBaseCoordinate canonicalLorentzianTimeDirection) *
          ⇑(localBaseCoordinate axis.succ)) candidate) •
            matterCoordinateEquiv response)
      point) (coordinateDirection direction) = _
  rw [correctionDerivative.fderiv]
  simp only [add_apply,
    ContinuousLinearMap.smulRight_apply]
  simp [localBaseCoordinate]
  module

@[simp] theorem
    matterMixedTimeSpatialCoordinateCorrection_directionalDerivative_origin
    (axis : Fin 3)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterMixedTimeSpatialCoordinateCorrection axis response)
        0 direction =
      0 := by
  rw [matterMixedTimeSpatialCoordinateCorrection_directionalDerivative]
  simp

theorem matterMixedTimeSpatialCoordinateCorrection_coordinate_smooth
    (axis : Fin 3)
    (response : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞
      (matterMixedTimeSpatialCoordinateCorrection axis response) := by
  have coefficientSmooth : ContDiff ℝ ∞
      (matterMixedTimeSpatialCoefficient axis) :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).contDiff.mul
      (localBaseCoordinate axis.succ).contDiff
  exact coefficientSmooth.smul contDiff_const

private theorem fieldDirectionalDerivative_add_matterCoordinate
    (first second : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (firstDifferentiable : DifferentiableAt ℝ first point)
    (secondDifferentiable : DifferentiableAt ℝ second point)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (first + second) point direction =
      fieldDirectionalDerivative first point direction +
        fieldDirectionalDerivative second point direction := by
  change fieldDirectionalDerivative
      (fun candidate => first candidate + second candidate) point direction = _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable,
    add_apply]

private theorem fieldDirectionalDerivative_finset_sum_matterCoordinate
    {Index : Type*} [Fintype Index]
    (field : Index → BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (fieldDifferentiable : ∀ index, DifferentiableAt ℝ (field index) point)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => ∑ index, field index candidate)
        point direction =
      ∑ index, fieldDirectionalDerivative (field index) point direction := by
  have sumDerivative :
      HasFDerivAt
        (∑ index, field index)
        (∑ index, fderiv ℝ (field index) point) point :=
    HasFDerivAt.sum (u := Finset.univ) fun index _ =>
      (fieldDifferentiable index).hasFDerivAt
  have sumDerivativePointwise :
      HasFDerivAt
        (fun candidate => ∑ index, field index candidate)
        (∑ index, fderiv ℝ (field index) point) point := by
    convert sumDerivative using 1
    funext candidate
    simp
  unfold fieldDirectionalDerivative
  rw [sumDerivativePointwise.fderiv]
  simp

theorem matterCompleteQuadraticCoordinateCorrection_directionalDerivative_time
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (matterCompleteQuadraticCoordinateCorrection hessian)
        point canonicalLorentzianTimeDirection =
      point canonicalLorentzianTimeDirection •
          matterCoordinateEquiv hessian.timeTime +
        ∑ axis : Fin 3,
          point axis.succ • matterCoordinateEquiv (hessian.timeSpatial axis) := by
  have timeDifferentiable : DifferentiableAt ℝ
      (matterQuadraticTimeCoordinateCorrection hessian.timeTime) point :=
    (matterQuadraticTimeCoordinateCorrection_coordinate_smooth hessian.timeTime)
      |>.differentiable (by simp) |>.differentiableAt
  have mixedDifferentiable : ∀ axis : Fin 3, DifferentiableAt ℝ
      (matterMixedTimeSpatialCoordinateCorrection axis
        (hessian.timeSpatial axis)) point := fun axis =>
    (matterMixedTimeSpatialCoordinateCorrection_coordinate_smooth axis
      (hessian.timeSpatial axis)).differentiable (by simp) |>.differentiableAt
  unfold matterCompleteQuadraticCoordinateCorrection
  change fieldDirectionalDerivative
      ((matterQuadraticTimeCoordinateCorrection hessian.timeTime) +
        fun candidate => ∑ axis : Fin 3,
          matterMixedTimeSpatialCoordinateCorrection axis
            (hessian.timeSpatial axis) candidate)
      point canonicalLorentzianTimeDirection = _
  rw [fieldDirectionalDerivative_add_matterCoordinate _ _ point
    timeDifferentiable ((ContDiff.sum fun axis _ =>
      matterMixedTimeSpatialCoordinateCorrection_coordinate_smooth axis
        (hessian.timeSpatial axis)).differentiable (by simp)
        |>.differentiableAt)]
  rw [fieldDirectionalDerivative_finset_sum_matterCoordinate _ point
    mixedDifferentiable]
  rw [matterQuadraticTimeCoordinateCorrection_directionalDerivative]
  simp [matterMixedTimeSpatialCoordinateCorrection_directionalDerivative,
    coordinateDirection, canonicalLorentzianTimeDirection]

theorem matterCompleteQuadraticCoordinateCorrection_directionalDerivative_spatial
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint)
    (axis : Fin 3) :
    fieldDirectionalDerivative
        (matterCompleteQuadraticCoordinateCorrection hessian)
        point axis.succ =
      point canonicalLorentzianTimeDirection •
        matterCoordinateEquiv (hessian.timeSpatial axis) := by
  have timeDifferentiable : DifferentiableAt ℝ
      (matterQuadraticTimeCoordinateCorrection hessian.timeTime) point :=
    (matterQuadraticTimeCoordinateCorrection_coordinate_smooth hessian.timeTime)
      |>.differentiable (by simp) |>.differentiableAt
  have mixedDifferentiable : ∀ otherAxis : Fin 3, DifferentiableAt ℝ
      (matterMixedTimeSpatialCoordinateCorrection otherAxis
        (hessian.timeSpatial otherAxis)) point := fun otherAxis =>
    (matterMixedTimeSpatialCoordinateCorrection_coordinate_smooth otherAxis
      (hessian.timeSpatial otherAxis)).differentiable (by simp)
      |>.differentiableAt
  unfold matterCompleteQuadraticCoordinateCorrection
  change fieldDirectionalDerivative
      ((matterQuadraticTimeCoordinateCorrection hessian.timeTime) +
        fun candidate => ∑ otherAxis : Fin 3,
          matterMixedTimeSpatialCoordinateCorrection otherAxis
            (hessian.timeSpatial otherAxis) candidate)
      point axis.succ = _
  rw [fieldDirectionalDerivative_add_matterCoordinate _ _ point
    timeDifferentiable ((ContDiff.sum fun otherAxis _ =>
      matterMixedTimeSpatialCoordinateCorrection_coordinate_smooth otherAxis
        (hessian.timeSpatial otherAxis)).differentiable (by simp)
        |>.differentiableAt)]
  rw [fieldDirectionalDerivative_finset_sum_matterCoordinate _ point
    mixedDifferentiable]
  rw [matterQuadraticTimeCoordinateCorrection_directionalDerivative]
  fin_cases axis <;>
    simp [matterMixedTimeSpatialCoordinateCorrection_directionalDerivative,
      coordinateDirection, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

@[simp] theorem matterCompleteQuadraticCoordinateCorrection_origin
    (hessian : TemporalPivotMatterHessian) :
    matterCompleteQuadraticCoordinateCorrection hessian 0 = 0 := by
  simp [matterCompleteQuadraticCoordinateCorrection]

theorem matterCompleteQuadraticCoordinateCorrection_eq_zero_of_time_zero
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint)
    (timeZero : point canonicalLorentzianTimeDirection = 0) :
    matterCompleteQuadraticCoordinateCorrection hessian point = 0 := by
  unfold matterCompleteQuadraticCoordinateCorrection
  rw [matterQuadraticTimeCoordinateCorrection]
  simp [scalarQuadraticTimeCoefficient, localBaseCoordinate, timeZero,
    matterMixedTimeSpatialCoordinateCorrection_eq_zero_of_time_zero _ _ point
      timeZero]

@[simp] theorem
    matterCompleteQuadraticCoordinateCorrection_directionalDerivative_origin
    (hessian : TemporalPivotMatterHessian)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterCompleteQuadraticCoordinateCorrection hessian) 0 direction =
      0 := by
  refine Fin.cases ?_ (fun axis => ?_) direction
  · change fieldDirectionalDerivative
      (matterCompleteQuadraticCoordinateCorrection hessian) 0
        canonicalLorentzianTimeDirection = 0
    rw [matterCompleteQuadraticCoordinateCorrection_directionalDerivative_time]
    simp
  · rw [matterCompleteQuadraticCoordinateCorrection_directionalDerivative_spatial]
    simp

private theorem coordinateSmulMatter_hasFDerivAt_origin
    (coordinate : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    HasFDerivAt
      (fun point : BasePoint =>
        point coordinate • matterCoordinateEquiv matter)
      ((localBaseCoordinate coordinate).smulRight
        (matterCoordinateEquiv matter)) 0 :=
  (localBaseCoordinate coordinate).hasFDerivAt.smul_const
    (matterCoordinateEquiv matter)

private theorem coordinateSmulMatter_directionalDerivative_origin
    (coordinate : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          point coordinate • matterCoordinateEquiv matter)
        0 direction =
      coordinateDirection direction coordinate •
        matterCoordinateEquiv matter := by
  unfold fieldDirectionalDerivative
  rw [(coordinateSmulMatter_hasFDerivAt_origin coordinate matter).fderiv]
  simp [localBaseCoordinate]

theorem matterCompleteQuadraticCoordinateCorrection_secondDerivative_origin
    (hessian : TemporalPivotMatterHessian)
    (first second : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (matterCompleteQuadraticCoordinateCorrection hessian) point first)
        0 second =
      matterCoordinateEquiv
        (temporalPivotMatterHessianValue hessian first second) := by
  refine Fin.cases ?_ (fun firstAxis => ?_) first
  · change fieldDirectionalDerivative
      (fun point => fieldDirectionalDerivative
        (matterCompleteQuadraticCoordinateCorrection hessian) point
          canonicalLorentzianTimeDirection) 0 second = _
    rw [show
      (fun point => fieldDirectionalDerivative
        (matterCompleteQuadraticCoordinateCorrection hessian) point
          canonicalLorentzianTimeDirection) =
        (fun point =>
          point canonicalLorentzianTimeDirection •
              matterCoordinateEquiv hessian.timeTime +
            ∑ axis : Fin 3,
              point axis.succ •
                matterCoordinateEquiv (hessian.timeSpatial axis)) by
      funext point
      exact
        matterCompleteQuadraticCoordinateCorrection_directionalDerivative_time
          hessian point]
    have timeDifferentiable : DifferentiableAt ℝ
        (fun point : BasePoint =>
          point canonicalLorentzianTimeDirection •
            matterCoordinateEquiv hessian.timeTime) 0 :=
      (coordinateSmulMatter_hasFDerivAt_origin
        canonicalLorentzianTimeDirection hessian.timeTime).differentiableAt
    have mixedDifferentiable : ∀ axis : Fin 3, DifferentiableAt ℝ
        (fun point : BasePoint =>
          point axis.succ •
            matterCoordinateEquiv (hessian.timeSpatial axis)) 0 := fun axis =>
      (coordinateSmulMatter_hasFDerivAt_origin axis.succ
        (hessian.timeSpatial axis)).differentiableAt
    have mixedSumDifferentiable : DifferentiableAt ℝ
        (fun point : BasePoint => ∑ axis : Fin 3,
          point axis.succ •
            matterCoordinateEquiv (hessian.timeSpatial axis)) 0 :=
      have mixedSumSmooth : ContDiff ℝ ∞
          (fun point : BasePoint => ∑ axis : Fin 3,
            point axis.succ •
              matterCoordinateEquiv (hessian.timeSpatial axis)) :=
        ContDiff.sum fun axis _ =>
          (localBaseCoordinate axis.succ).contDiff.smul contDiff_const
      mixedSumSmooth.differentiable (by simp) |>.differentiableAt
    change fieldDirectionalDerivative
      ((fun point : BasePoint =>
        point canonicalLorentzianTimeDirection •
          matterCoordinateEquiv hessian.timeTime) +
        fun point => ∑ axis : Fin 3,
          point axis.succ •
            matterCoordinateEquiv (hessian.timeSpatial axis)) 0 second = _
    rw [fieldDirectionalDerivative_add_matterCoordinate _ _ 0
      timeDifferentiable mixedSumDifferentiable]
    rw [fieldDirectionalDerivative_finset_sum_matterCoordinate _ 0
      mixedDifferentiable]
    rw [coordinateSmulMatter_directionalDerivative_origin]
    simp_rw [coordinateSmulMatter_directionalDerivative_origin]
    refine Fin.cases ?_ (fun secondAxis => ?_) second
    · simp [canonicalLorentzianTimeDirection, coordinateDirection,
        temporalPivotMatterHessianValue]
    · fin_cases secondAxis <;>
        simp [canonicalLorentzianTimeDirection, coordinateDirection,
          temporalPivotMatterHessianValue, Matrix.cons_val,
          Fin.sum_univ_three]
  · rw [show
      (fun point => fieldDirectionalDerivative
        (matterCompleteQuadraticCoordinateCorrection hessian) point
          firstAxis.succ) =
        (fun point =>
          point canonicalLorentzianTimeDirection •
            matterCoordinateEquiv (hessian.timeSpatial firstAxis)) by
      funext point
      exact
        matterCompleteQuadraticCoordinateCorrection_directionalDerivative_spatial
          hessian point firstAxis]
    have derivative :=
      coordinateSmulMatter_hasFDerivAt_origin
        canonicalLorentzianTimeDirection (hessian.timeSpatial firstAxis)
    refine Fin.cases ?_ (fun secondAxis => ?_) second
    · change fieldDirectionalDerivative
        (fun point : BasePoint =>
          point canonicalLorentzianTimeDirection •
            matterCoordinateEquiv (hessian.timeSpatial firstAxis))
        0 canonicalLorentzianTimeDirection =
          matterCoordinateEquiv
            (temporalPivotMatterHessianValue hessian firstAxis.succ
              canonicalLorentzianTimeDirection)
      unfold fieldDirectionalDerivative
      rw [derivative.fderiv]
      simp [canonicalLorentzianTimeDirection, coordinateDirection]
      rw [show (0 : LorentzianIndex) =
        canonicalLorentzianTimeDirection by rfl,
        temporalPivotMatterHessianValue_spatial_time]
    · unfold fieldDirectionalDerivative
      rw [derivative.fderiv]
      simp [canonicalLorentzianTimeDirection, coordinateDirection]

theorem matterCompleteQuadraticCoordinateCorrection_coordinate_smooth
    (hessian : TemporalPivotMatterHessian) :
    ContDiff ℝ ∞ (matterCompleteQuadraticCoordinateCorrection hessian) :=
  (matterQuadraticTimeCoordinateCorrection_coordinate_smooth hessian.timeTime).add
    (ContDiff.sum fun axis _ =>
      matterMixedTimeSpatialCoordinateCorrection_coordinate_smooth axis
        (hessian.timeSpatial axis))

@[simp] theorem matterCompleteQuadraticCoordinateCorrection_zero :
    matterCompleteQuadraticCoordinateCorrection 0 = 0 := by
  funext point
  simp [matterCompleteQuadraticCoordinateCorrection,
    matterQuadraticTimeCoordinateCorrection,
    matterMixedTimeSpatialCoordinateCorrection]

/-! ## Installation and faithful Cauchy-slice realization -/

/-- Install only the canonical temporal-pivot matter second jet. -/
def installMatterCompleteFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    StageNineHolonomicConfiguration :=
  varyMatterCoordinates configuration
    (matterCompleteQuadraticCoordinateCorrection hessian) 1

@[simp] theorem installMatterCompleteFirstGermResponse_coframe
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem installMatterCompleteFirstGermResponse_gravityConnection
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem installMatterCompleteFirstGermResponse_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).gravityAuxiliary =
      configuration.gravityAuxiliary :=
  rfl

@[simp] theorem installMatterCompleteFirstGermResponse_gravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).gravitySimplicityMultiplier =
      configuration.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem installMatterCompleteFirstGermResponse_gaugeConnection
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem installMatterCompleteFirstGermResponse_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).gaugeAuxiliary =
      configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem installMatterCompleteFirstGermResponse_scalar
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem installMatterCompleteFirstGermResponse_conjugateMatter
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).conjugateMatter =
      configuration.conjugateMatter :=
  rfl

theorem installMatterCompleteFirstGermResponse_matter_coordinate
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    matterCoordinateEquiv
        ((installMatterCompleteFirstGermResponse configuration hessian).matter
          point) =
      matterCoordinateEquiv (configuration.matter point) +
        matterCompleteQuadraticCoordinateCorrection hessian point := by
  simp [installMatterCompleteFirstGermResponse, varyMatterCoordinates]

/-- The spatial--spatial Hessian block is fixed to zero precisely so the
complete correction preserves the entire initial Cauchy slice, not only its
origin. -/
theorem installMatterCompleteFirstGermResponse_matter_of_time_zero
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint)
    (timeZero : point canonicalLorentzianTimeDirection = 0) :
    (installMatterCompleteFirstGermResponse configuration hessian).matter point =
      configuration.matter point := by
  apply matterCoordinateEquiv.injective
  rw [installMatterCompleteFirstGermResponse_matter_coordinate]
  rw [matterCompleteQuadraticCoordinateCorrection_eq_zero_of_time_zero
    hessian point timeZero, add_zero]

@[simp] theorem installMatterCompleteFirstGermResponse_matter_origin
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).matter 0 =
      configuration.matter 0 := by
  exact installMatterCompleteFirstGermResponse_matter_of_time_zero
    configuration hessian 0 (by simp)

theorem installMatterCompleteFirstGermResponse_matter_firstJet_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((installMatterCompleteFirstGermResponse configuration hessian).matter
            point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (configuration.matter point))
        0 direction := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (configuration.matter point)) 0 :=
    (smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have correctionDifferentiable : DifferentiableAt ℝ
      (matterCompleteQuadraticCoordinateCorrection hessian) 0 :=
    (matterCompleteQuadraticCoordinateCorrection_coordinate_smooth hessian)
      |>.differentiable (by simp) |>.differentiableAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point => matterCoordinateEquiv
      ((installMatterCompleteFirstGermResponse configuration hessian).matter
        point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterCompleteQuadraticCoordinateCorrection hessian by
    funext point
    exact installMatterCompleteFirstGermResponse_matter_coordinate
      configuration hessian point]
  rw [fderiv_add backgroundDifferentiable correctionDifferentiable]
  change
    (fderiv ℝ (fun point => matterCoordinateEquiv (configuration.matter point)) 0 +
        fderiv ℝ (matterCompleteQuadraticCoordinateCorrection hessian) 0)
        (coordinateDirection direction) = _
  rw [add_apply]
  have correctionZero :=
    matterCompleteQuadraticCoordinateCorrection_directionalDerivative_origin
      hessian direction
  unfold fieldDirectionalDerivative at correctionZero
  rw [correctionZero, add_zero]

theorem installMatterCompleteFirstGermResponse_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, ?_, conjugateMatterSmooth⟩
  rw [show
    (fun point => matterCoordinateEquiv
      ((installMatterCompleteFirstGermResponse configuration hessian).matter
        point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterCompleteQuadraticCoordinateCorrection hessian by
    funext point
    exact installMatterCompleteFirstGermResponse_matter_coordinate
      configuration hessian point]
  exact matterSmooth.add
    (matterCompleteQuadraticCoordinateCorrection_coordinate_smooth hessian)

theorem installMatterCompleteFirstGermResponse_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (hessian : TemporalPivotMatterHessian) :
    (installMatterCompleteFirstGermResponse configuration hessian).Nondegenerate := by
  simpa [StageNineHolonomicConfiguration.Nondegenerate] using nondegenerate

theorem installMatterCompleteFirstGermResponse_zero
    (configuration : StageNineHolonomicConfiguration) :
    installMatterCompleteFirstGermResponse configuration 0 = configuration := by
  cases configuration
  simp [installMatterCompleteFirstGermResponse, varyMatterCoordinates]

/-- The realization is faithful on the complete temporal-pivot carrier.  Its
proof reads the actual quadratic increment's Hessian, so none of the three
mixed responses can disappear into an unobserved sink. -/
theorem installMatterCompleteFirstGermResponse_eq_iff
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    installMatterCompleteFirstGermResponse configuration hessian =
        configuration ↔
      hessian = 0 := by
  constructor
  · intro actualEq
    have correctionPointZero (point : BasePoint) :
        matterCompleteQuadraticCoordinateCorrection hessian point = 0 := by
      have matterEq := congrArg
        (fun candidate : StageNineHolonomicConfiguration =>
          matterCoordinateEquiv (candidate.matter point)) actualEq
      rw [installMatterCompleteFirstGermResponse_matter_coordinate] at matterEq
      exact add_left_cancel
        (show
          matterCoordinateEquiv (configuration.matter point) +
                matterCompleteQuadraticCoordinateCorrection hessian point =
              matterCoordinateEquiv (configuration.matter point) + 0 by
          simpa using matterEq)
    have correctionFunctionZero :
        matterCompleteQuadraticCoordinateCorrection hessian = 0 := by
      funext point
      exact correctionPointZero point
    have hessianValueZero (first second : LorentzianIndex) :
        temporalPivotMatterHessianValue hessian first second = 0 := by
      apply matterCoordinateEquiv.injective
      have derivativeEq := congrArg
        (fun field : BasePoint → MatterCoordinateCarrier =>
          fieldDirectionalDerivative
            (fun point => fieldDirectionalDerivative field point first)
            0 second)
        correctionFunctionZero
      rw [matterCompleteQuadraticCoordinateCorrection_secondDerivative_origin]
        at derivativeEq
      simpa [fieldDirectionalDerivative] using derivativeEq
    apply TemporalPivotMatterHessian.ext
    · simpa using hessianValueZero canonicalLorentzianTimeDirection
        canonicalLorentzianTimeDirection
    · funext axis
      simpa using hessianValueZero canonicalLorentzianTimeDirection axis.succ
  · rintro rfl
    exact installMatterCompleteFirstGermResponse_zero configuration

/-! ## Complete Hessian principal readout -/

theorem matterCompleteQuadraticCoordinateCorrection_directionalDerivative_normalForm
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterCompleteQuadraticCoordinateCorrection hessian) point direction =
      ∑ second : LorentzianIndex,
        point second • matterCoordinateEquiv
          (temporalPivotMatterHessianValue hessian direction second) := by
  refine Fin.cases ?_ (fun axis => ?_) direction
  · change fieldDirectionalDerivative
      (matterCompleteQuadraticCoordinateCorrection hessian) point
        canonicalLorentzianTimeDirection = _
    rw [matterCompleteQuadraticCoordinateCorrection_directionalDerivative_time,
      Fin.sum_univ_four, Fin.sum_univ_three]
    simp [canonicalLorentzianTimeDirection,
      temporalPivotMatterHessianValue, Matrix.cons_val]
    module
  · rw [matterCompleteQuadraticCoordinateCorrection_directionalDerivative_spatial,
      Fin.sum_univ_four]
    fin_cases axis <;>
      simp [canonicalLorentzianTimeDirection,
        temporalPivotMatterHessianValue, Matrix.cons_val]

private theorem identityCoframeMatterPrincipal_real_smul
    (direction : LorentzianIndex)
    (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    identityCoframeMatterPrincipal direction (parameter • matter) =
      parameter • identityCoframeMatterPrincipal direction matter :=
  (identityCoframeMatterPrincipal direction).map_smul_of_tower parameter matter

theorem matterCompleteQuadraticPrincipal_normalForm
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    (∑ direction : LorentzianIndex,
      identityCoframeMatterPrincipal direction
        (matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (matterCompleteQuadraticCoordinateCorrection hessian)
            point direction))) =
      ∑ derivativeDirection : LorentzianIndex,
        point derivativeDirection •
          completeMatterFirstGermPrincipalResponse hessian
            derivativeDirection := by
  simp_rw [matterCompleteQuadraticCoordinateCorrection_directionalDerivative_normalForm]
  simp_rw [map_sum, matterCoordinateEquiv_symm_real_smul,
    matterCoordinateEquiv.symm_apply_apply,
    identityCoframeMatterPrincipal_real_smul]
  unfold completeMatterFirstGermPrincipalResponse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact (Finset.smul_sum
    (M := ℝ) (N := DiracExteriorMatterCarrier)
    (r := point derivativeDirection)
    (f := fun direction : LorentzianIndex =>
      identityCoframeMatterPrincipal direction
        (temporalPivotMatterHessianValue hessian direction
          derivativeDirection))
    (s := Finset.univ)).symm

/-! ## Installation as an actual matter variation -/

theorem matterCoordinateDerivative_installMatterCompleteFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv
          ((installMatterCompleteFirstGermResponse configuration hessian).matter
            candidate))
        point direction =
      fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv
            (configuration.matter candidate))
          point direction +
        matterVariationCoordinateDerivative
          (matterCompleteQuadraticCoordinateCorrection hessian)
          point direction := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun candidate => matterCoordinateEquiv
        (configuration.matter candidate)) point :=
    (smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have correctionDifferentiable : DifferentiableAt ℝ
      (matterCompleteQuadraticCoordinateCorrection hessian) point :=
    (matterCompleteQuadraticCoordinateCorrection_coordinate_smooth hessian)
      |>.differentiable (by simp) |>.differentiableAt
  unfold fieldDirectionalDerivative matterVariationCoordinateDerivative
  rw [show
    (fun candidate => matterCoordinateEquiv
      ((installMatterCompleteFirstGermResponse configuration hessian).matter
        candidate)) =
      (fun candidate => matterCoordinateEquiv
        (configuration.matter candidate)) +
        matterCompleteQuadraticCoordinateCorrection hessian by
    funext candidate
    exact installMatterCompleteFirstGermResponse_matter_coordinate
      configuration hessian candidate]
  rw [fderiv_add backgroundDifferentiable correctionDifferentiable, add_apply]
  rfl

theorem
    holonomicMatterCovariantDerivative_installMatterCompleteFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (installMatterCompleteFirstGermResponse configuration hessian)
        point direction =
      holonomicMatterCovariantDerivative configuration point direction +
        holonomicMatterVariationCovariantDerivative configuration
          (matterCompleteQuadraticCoordinateCorrection hessian)
          point direction := by
  unfold holonomicMatterCovariantDerivative
    holonomicMatterVariationCovariantDerivative
  rw [matterCoordinateDerivative_installMatterCompleteFirstGermResponse
    configuration smooth]
  simp only [installMatterCompleteFirstGermResponse,
    varyMatterCoordinates, matterCoordinateEquiv.symm_apply_apply,
    map_add, one_smul]
  module

theorem toContinuumPointField_installMatterCompleteFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    toContinuumPointField
        (installMatterCompleteFirstGermResponse configuration hessian) point =
      withMatterJets (toContinuumPointField configuration point)
        (configuration.matter point +
          matterCoordinateEquiv.symm
            (matterCompleteQuadraticCoordinateCorrection hessian point))
        (holonomicMatterCovariantDerivative configuration point +
          holonomicMatterVariationCovariantDerivative configuration
            (matterCompleteQuadraticCoordinateCorrection hessian) point) := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  · simp [toContinuumPointField, withMatterJets,
      installMatterCompleteFirstGermResponse, varyMatterCoordinates, map_add]
  · funext direction
    exact
      holonomicMatterCovariantDerivative_installMatterCompleteFirstGermResponse
        configuration smooth hessian point direction

theorem generatedContinuumMatterVector_installMatterCompleteFirstGermResponse
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    generatedContinuumMatterVector source 0 point
        (toContinuumPointField
          (installMatterCompleteFirstGermResponse configuration hessian) point) =
      generatedContinuumMatterVector source 0 point
          (toContinuumPointField configuration point) +
        matterFieldVariationVector source point
          (toContinuumPointField configuration point)
          (matterCoordinateEquiv.symm
            (matterCompleteQuadraticCoordinateCorrection hessian point))
          (holonomicMatterVariationCovariantDerivative configuration
            (matterCompleteQuadraticCoordinateCorrection hessian) point) := by
  rw [toContinuumPointField_installMatterCompleteFirstGermResponse
    configuration smooth]
  let matterVariation := matterCoordinateEquiv.symm
    (matterCompleteQuadraticCoordinateCorrection hessian point)
  let derivativeVariation :=
    holonomicMatterVariationCovariantDerivative configuration
      (matterCompleteQuadraticCoordinateCorrection hessian) point
  have matterOne : (1 : ℝ) • matterVariation = matterVariation := by
    change (1 : ℂ) • matterVariation = matterVariation
    exact one_smul ℂ matterVariation
  have derivativeOne : (1 : ℝ) • derivativeVariation = derivativeVariation := by
    funext direction
    change (1 : ℂ) • derivativeVariation direction = derivativeVariation direction
    exact one_smul ℂ (derivativeVariation direction)
  have responseOne :
      (1 : ℝ) • matterFieldVariationVector source point
          (toContinuumPointField configuration point)
          matterVariation derivativeVariation =
        matterFieldVariationVector source point
          (toContinuumPointField configuration point)
          matterVariation derivativeVariation := by
    change (1 : ℂ) • matterFieldVariationVector source point
        (toContinuumPointField configuration point)
        matterVariation derivativeVariation = _
    exact one_smul ℂ _
  have affine :=
    generatedContinuumMatterVector_withMatterJets_affine source point
      (toContinuumPointField configuration point)
      matterVariation derivativeVariation 1
  rw [matterOne, derivativeOne, responseOne] at affine
  simpa [matterVariation, derivativeVariation, toContinuumPointField] using affine

theorem generatedContinuumMatterVector_installMatterCompleteFirstGermResponse_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField
          (installMatterCompleteFirstGermResponse configuration hessian) 0) =
      generatedContinuumMatterVector source 0 0
        (toContinuumPointField configuration 0) := by
  rw [generatedContinuumMatterVector_installMatterCompleteFirstGermResponse
    source configuration smooth]
  have covariantVariationZero :
      holonomicMatterVariationCovariantDerivative configuration
          (matterCompleteQuadraticCoordinateCorrection hessian) 0 =
        0 :=
    holonomicMatterVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration (matterCompleteQuadraticCoordinateCorrection hessian) 0
      (matterCompleteQuadraticCoordinateCorrection_origin hessian)
      (matterCompleteQuadraticCoordinateCorrection_directionalDerivative_origin
        hessian)
  rw [matterCompleteQuadraticCoordinateCorrection_origin, map_zero,
    covariantVariationZero, matterFieldVariationVector_zero, add_zero]

/-! ## Complete actual variation normal form -/

theorem matterCompleteVariationCovariantDerivative_normalForm
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicMatterVariationCovariantDerivative configuration
        (matterCompleteQuadraticCoordinateCorrection hessian) point direction =
      matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (matterCompleteQuadraticCoordinateCorrection hessian)
            point direction) +
        matterQuadraticConnectionAction configuration
          (matterCoordinateEquiv.symm
            (matterCompleteQuadraticCoordinateCorrection hessian point))
          point direction := by
  unfold holonomicMatterVariationCovariantDerivative
    matterVariationCoordinateDerivative matterQuadraticConnectionAction
  module

/-- The zero-order connection/Yukawa response to the complete quadratic
carrier.  It will be proved to have zero first germ at the origin. -/
def matterCompleteQuadraticDiracRemainder
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        diracMatrixMatterAction (DiracCliffordRepresentation.diracGamma direction)
          (matterQuadraticConnectionAction configuration
            (matterCoordinateEquiv.symm
              (matterCompleteQuadraticCoordinateCorrection hessian point))
            point direction) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))
      (matterCoordinateEquiv.symm
        (matterCompleteQuadraticCoordinateCorrection hessian point))

theorem matterCompleteQuadraticVariationVector_normalForm
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    matterFieldVariationVector source point
        (toContinuumPointField configuration point)
        (matterCoordinateEquiv.symm
          (matterCompleteQuadraticCoordinateCorrection hessian point))
        (holonomicMatterVariationCovariantDerivative configuration
          (matterCompleteQuadraticCoordinateCorrection hessian) point) =
      (∑ derivativeDirection : LorentzianIndex,
        point derivativeDirection •
          completeMatterFirstGermPrincipalResponse hessian
            derivativeDirection) +
        matterCompleteQuadraticDiracRemainder configuration hessian point := by
  have coframePoint : configuration.coframe point = 1 :=
    congrFun identityCoframe point
  have gammaIdentity (direction : LorentzianIndex) :
      inverseCoframeDiracGamma
          { coframe := configuration.coframe point, derivative := 0 }
          direction =
        DiracCliffordRepresentation.diracGamma direction := by
    rw [coframePoint]
    change inverseCoframeDiracGamma identityCoframeMatterGeometry direction =
      DiracCliffordRepresentation.diracGamma direction
    exact inverseCoframeDiracGamma_identity direction
  have kineticPrincipal :
      Complex.I •
          ∑ direction : LorentzianIndex,
            diracMatrixMatterAction
              (DiracCliffordRepresentation.diracGamma direction)
              (matterCoordinateEquiv.symm
                (fieldDirectionalDerivative
                  (matterCompleteQuadraticCoordinateCorrection hessian)
                  point direction)) =
        ∑ direction : LorentzianIndex,
          identityCoframeMatterPrincipal direction
            (matterCoordinateEquiv.symm
              (fieldDirectionalDerivative
                (matterCompleteQuadraticCoordinateCorrection hessian)
                point direction)) := by
    rw [Finset.smul_sum]
    rfl
  unfold matterFieldVariationVector
  rw [matterGaugeKineticSum_zeroChart]
  simp only [toContinuumPointField]
  simp_rw [gammaIdentity]
  simp_rw [matterCompleteVariationCovariantDerivative_normalForm]
  simp_rw [map_add]
  rw [Finset.sum_add_distrib, smul_add, kineticPrincipal,
    matterCompleteQuadraticPrincipal_normalForm]
  unfold matterCompleteQuadraticDiracRemainder
  module

theorem matterCompleteQuadraticCorrectionCarrier_normalForm
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    matterCoordinateEquiv.symm
        (matterCompleteQuadraticCoordinateCorrection hessian point) =
      scalarQuadraticTimeCoefficient point • hessian.timeTime +
        ∑ axis : Fin 3,
          matterMixedTimeSpatialCoefficient axis point •
            hessian.timeSpatial axis := by
  unfold matterCompleteQuadraticCoordinateCorrection
    matterQuadraticTimeCoordinateCorrection
    matterMixedTimeSpatialCoordinateCorrection
  rw [map_add, map_sum]
  simp_rw [matterCoordinateEquiv_symm_real_smul,
    matterCoordinateEquiv.symm_apply_apply]

private theorem matterQuadraticConnectionAction_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    matterQuadraticConnectionAction configuration (first + second)
        point direction =
      matterQuadraticConnectionAction configuration first point direction +
        matterQuadraticConnectionAction configuration second point direction := by
  unfold matterQuadraticConnectionAction
  simp only [map_add]
  module

private theorem matterQuadraticConnectionAction_real_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    matterQuadraticConnectionAction configuration (parameter • matter)
        point direction =
      parameter •
        matterQuadraticConnectionAction configuration matter point direction := by
  unfold matterQuadraticConnectionAction
  rw [diracMatrixMatterAction_real_smul,
    diracExteriorMotherLieAction_matter_real_smul]
  module

private theorem matterQuadraticDiracRemainder_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterQuadraticDiracRemainder configuration (first + second) point =
      matterQuadraticDiracRemainder configuration first point +
        matterQuadraticDiracRemainder configuration second point := by
  unfold matterQuadraticDiracRemainder
  simp_rw [matterQuadraticConnectionAction_add, map_add]
  rw [Finset.sum_add_distrib, smul_add]
  module

private theorem matterQuadraticDiracRemainder_real_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterQuadraticDiracRemainder configuration (parameter • matter) point =
      parameter • matterQuadraticDiracRemainder configuration matter point := by
  unfold matterQuadraticDiracRemainder
  simp_rw [matterQuadraticConnectionAction_real_smul,
    diracMatrixMatterAction_real_smul]
  have connectionSum :
      (∑ direction : LorentzianIndex,
        parameter •
          diracMatrixMatterAction
            (DiracCliffordRepresentation.diracGamma direction)
            (matterQuadraticConnectionAction configuration matter point
              direction)) =
        parameter •
          ∑ direction : LorentzianIndex,
            diracMatrixMatterAction
              (DiracCliffordRepresentation.diracGamma direction)
              (matterQuadraticConnectionAction configuration matter point
                direction) :=
    (Finset.smul_sum
      (M := ℝ) (N := DiracExteriorMatterCarrier)
      (r := parameter)
      (f := fun direction : LorentzianIndex =>
        diracMatrixMatterAction
          (DiracCliffordRepresentation.diracGamma direction)
          (matterQuadraticConnectionAction configuration matter point
            direction))
      (s := Finset.univ)).symm
  rw [connectionSum]
  rw [chiralExteriorYukawaAction_matter_real_smul]
  rw [smul_comm Complex.I parameter]
  module

/-- Coordinate form of the zero-order remainder, displayed as the same four
fixed matter carriers weighted by their canonical quadratic monomials. -/
def matterCompleteQuadraticWeightedRemainderCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian) :
    BasePoint → MatterCoordinateCarrier :=
  (fun point =>
    scalarQuadraticTimeCoefficient point •
      matterCoordinateEquiv
        (matterQuadraticDiracRemainder configuration hessian.timeTime point)) +
    ∑ axis : Fin 3, fun point =>
      matterMixedTimeSpatialCoefficient axis point •
        matterCoordinateEquiv
          (matterQuadraticDiracRemainder configuration
            (hessian.timeSpatial axis) point)

theorem matterCompleteQuadraticDiracRemainder_coordinate_normalForm
    (configuration : StageNineHolonomicConfiguration)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    matterCoordinateEquiv
        (matterCompleteQuadraticDiracRemainder configuration hessian point) =
      matterCompleteQuadraticWeightedRemainderCoordinate configuration hessian
        point := by
  change matterCoordinateEquiv
      (matterQuadraticDiracRemainder configuration
        (matterCoordinateEquiv.symm
          (matterCompleteQuadraticCoordinateCorrection hessian point)) point) = _
  rw [matterCompleteQuadraticCorrectionCarrier_normalForm]
  simp [matterCompleteQuadraticWeightedRemainderCoordinate,
    matterQuadraticDiracRemainder_add,
    matterQuadraticDiracRemainder_real_smul, map_add,
    matterCoordinateEquiv_real_smul, Fin.sum_univ_three]

private theorem matterMixedTimeSpatialCoefficient_hasFDerivAt_origin_zero
    (axis : Fin 3) :
    HasFDerivAt (matterMixedTimeSpatialCoefficient axis)
      (0 : BasePoint →L[ℝ] ℝ) 0 := by
  have productDerivative :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := (0 : BasePoint)) |>.mul
        ((localBaseCoordinate axis.succ).hasFDerivAt (x := (0 : BasePoint)))
  change HasFDerivAt
    ((⇑(localBaseCoordinate canonicalLorentzianTimeDirection) :
        BasePoint → ℝ) *
      (⇑(localBaseCoordinate axis.succ) : BasePoint → ℝ))
    (0 : BasePoint →L[ℝ] ℝ) 0
  simpa only [map_zero, zero_smul, add_zero, smul_zero] using
    productDerivative

private theorem
    matterMixedQuadraticWeightedRemainder_hasFDerivAt_origin_zero
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (axis : Fin 3)
    (matter : DiracExteriorMatterCarrier) :
    HasFDerivAt
      (fun point =>
        matterMixedTimeSpatialCoefficient axis point •
          matterCoordinateEquiv
            (matterQuadraticDiracRemainder configuration matter point))
      (0 : BasePoint →L[ℝ] MatterCoordinateCarrier) 0 := by
  have remainderDifferentiableAt : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv
        (matterQuadraticDiracRemainder configuration matter point)) 0 :=
    (matterQuadraticDiracRemainder_coordinate_smooth
      configuration smooth matter).differentiable (by simp)
      |>.differentiableAt
  have productDerivative :=
    (matterMixedTimeSpatialCoefficient_hasFDerivAt_origin_zero axis).smul
      remainderDifferentiableAt.hasFDerivAt
  change HasFDerivAt
    (matterMixedTimeSpatialCoefficient axis • fun point =>
      matterCoordinateEquiv
        (matterQuadraticDiracRemainder configuration matter point))
    (0 : BasePoint →L[ℝ] MatterCoordinateCarrier) 0
  simpa only [matterMixedTimeSpatialCoefficient_origin, zero_smul, zero_add,
    add_zero, ContinuousLinearMap.zero_smulRight] using productDerivative

theorem
    matterCompleteQuadraticWeightedRemainder_hasFDerivAt_origin_zero
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (hessian : TemporalPivotMatterHessian) :
    HasFDerivAt
      (matterCompleteQuadraticWeightedRemainderCoordinate configuration hessian)
      (0 : BasePoint →L[ℝ] MatterCoordinateCarrier) 0 := by
  have timeDerivative :=
    matterQuadraticWeightedRemainder_hasFDerivAt_origin_zero
      configuration smooth hessian.timeTime
  have mixedDerivative : ∀ axis : Fin 3, HasFDerivAt
      (fun point =>
        matterMixedTimeSpatialCoefficient axis point •
          matterCoordinateEquiv
            (matterQuadraticDiracRemainder configuration
              (hessian.timeSpatial axis) point))
      (0 : BasePoint →L[ℝ] MatterCoordinateCarrier) 0 := fun axis =>
    matterMixedQuadraticWeightedRemainder_hasFDerivAt_origin_zero
      configuration smooth axis (hessian.timeSpatial axis)
  unfold matterCompleteQuadraticWeightedRemainderCoordinate
  simpa using timeDerivative.add
    (HasFDerivAt.sum (u := Finset.univ) fun axis _ => mixedDerivative axis)

/-! ## Full four-direction Dirac first-germ shift -/

def matterCompleteLinearPrincipalCoordinate
    (hessian : TemporalPivotMatterHessian) :
    BasePoint → MatterCoordinateCarrier :=
  ∑ derivativeDirection : LorentzianIndex, fun point =>
    point derivativeDirection •
      matterCoordinateEquiv
        (completeMatterFirstGermPrincipalResponse hessian
          derivativeDirection)

theorem matterCompleteLinearPrincipalCoordinate_hasFDerivAt_origin
    (hessian : TemporalPivotMatterHessian) :
    HasFDerivAt (matterCompleteLinearPrincipalCoordinate hessian)
      (∑ derivativeDirection : LorentzianIndex,
        (localBaseCoordinate derivativeDirection).smulRight
          (matterCoordinateEquiv
            (completeMatterFirstGermPrincipalResponse hessian
              derivativeDirection))) 0 := by
  unfold matterCompleteLinearPrincipalCoordinate
  exact HasFDerivAt.sum (u := Finset.univ) fun direction _ =>
    (localBaseCoordinate direction).hasFDerivAt.smul_const
      (matterCoordinateEquiv
        (completeMatterFirstGermPrincipalResponse hessian direction))

private theorem matterCompleteLinearPrincipalDerivative_apply
    (hessian : TemporalPivotMatterHessian)
    (direction : LorentzianIndex) :
    (∑ derivativeDirection : LorentzianIndex,
      (localBaseCoordinate derivativeDirection).smulRight
        (matterCoordinateEquiv
          (completeMatterFirstGermPrincipalResponse hessian
            derivativeDirection)))
        (coordinateDirection direction) =
      matterCoordinateEquiv
        (completeMatterFirstGermPrincipalResponse hessian direction) := by
  fin_cases direction <;>
    simp [Fin.sum_univ_four, localBaseCoordinate, coordinateDirection]

theorem holonomicDiracYukawaCoordinateVector_install_complete_normalForm
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (hessian : TemporalPivotMatterHessian)
    (point : BasePoint) :
    holonomicDiracYukawaCoordinateVector source
        (installMatterCompleteFirstGermResponse configuration hessian) point =
      holonomicDiracYukawaCoordinateVector source configuration point +
        (matterCompleteLinearPrincipalCoordinate hessian point +
          matterCompleteQuadraticWeightedRemainderCoordinate configuration
            hessian point) := by
  unfold holonomicDiracYukawaCoordinateVector
  rw [generatedContinuumMatterVector_installMatterCompleteFirstGermResponse
    source configuration smooth, map_add]
  rw [matterCompleteQuadraticVariationVector_normalForm source configuration
    identityCoframe hessian point, map_add]
  simp only [map_sum, matterCoordinateEquiv_real_smul]
  rw [matterCompleteQuadraticDiracRemainder_coordinate_normalForm]
  unfold matterCompleteLinearPrincipalCoordinate
  simp

theorem holonomicDiracYukawaCoordinateVector_install_completeFirstGerm
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (hessian : TemporalPivotMatterHessian)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (holonomicDiracYukawaCoordinateVector source
          (installMatterCompleteFirstGermResponse configuration hessian))
        0 direction =
      fieldDirectionalDerivative
          (holonomicDiracYukawaCoordinateVector source configuration)
          0 direction +
        matterCoordinateEquiv
          (completeMatterFirstGermPrincipalResponse hessian direction) := by
  have baseDifferentiable : DifferentiableAt ℝ
      (holonomicDiracYukawaCoordinateVector source configuration) 0 :=
    (holonomicDiracYukawaCoordinateVector_contDiffAt_origin source
      configuration smooth identityCoframe).differentiableAt (by simp)
  have linearDerivative :=
    matterCompleteLinearPrincipalCoordinate_hasFDerivAt_origin hessian
  have remainderDerivative :=
    matterCompleteQuadraticWeightedRemainder_hasFDerivAt_origin_zero
      configuration smooth hessian
  rw [show
    holonomicDiracYukawaCoordinateVector source
        (installMatterCompleteFirstGermResponse configuration hessian) =
      holonomicDiracYukawaCoordinateVector source configuration +
        (matterCompleteLinearPrincipalCoordinate hessian +
          matterCompleteQuadraticWeightedRemainderCoordinate configuration
            hessian) by
    funext point
    exact holonomicDiracYukawaCoordinateVector_install_complete_normalForm
      source configuration smooth identityCoframe hessian point]
  unfold fieldDirectionalDerivative
  rw [(baseDifferentiable.hasFDerivAt.add
    (linearDerivative.add remainderDerivative)).fderiv]
  simp only [add_apply, add_zero]
  rw [matterCompleteLinearPrincipalDerivative_apply]

/-! ## Internally generated complete response -/

/-- The complete four-direction primal Dirac--Yukawa first-germ residual is
read only after the actual configuration exists. -/
def matterCompleteDiracYukawaFirstGermResidual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    LorentzianIndex → DiracExteriorMatterCarrier := fun direction =>
  matterCoordinateEquiv.symm
    (fieldDirectionalDerivative
      (holonomicDiracYukawaCoordinateVector source configuration)
      0 direction)

theorem matterCompleteDiracYukawaFirstGermResidual_coordinate
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzianIndex) :
    matterCoordinateEquiv
        (matterCompleteDiracYukawaFirstGermResidual source configuration
          direction) =
      fieldDirectionalDerivative
        (holonomicDiracYukawaCoordinateVector source configuration)
        0 direction := by
  simp [matterCompleteDiracYukawaFirstGermResidual]

/-- The branch-free symmetric Hessian generated from the actual complete
first germ. -/
def actionGeneratedMatterCompleteFirstGermHessian
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    TemporalPivotMatterHessian :=
  canonicalCompleteMatterFirstGermHessian
    (matterCompleteDiracYukawaFirstGermResidual source configuration)

/-- The same actual, updated only by the internally generated complete matter
second jet. -/
def actionGeneratedMatterCompleteFirstGermActual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installMatterCompleteFirstGermResponse configuration
    (actionGeneratedMatterCompleteFirstGermHessian source configuration)

theorem actionGeneratedMatterCompleteFirstGermHessian_unique
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (candidate : TemporalPivotMatterHessian)
    (candidateLaw : CompleteMatterFirstGermResponseLaw
      (matterCompleteDiracYukawaFirstGermResidual source configuration)
      candidate) :
    candidate =
      actionGeneratedMatterCompleteFirstGermHessian source configuration := by
  unfold actionGeneratedMatterCompleteFirstGermHessian
  exact completeMatterFirstGermResponseLaw_unique _ candidate candidateLaw

theorem actionGeneratedMatterCompleteFirstGermHessian_eq_zero_iff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedMatterCompleteFirstGermHessian source configuration = 0 ↔
      matterCompleteDiracYukawaFirstGermResidual source configuration = 0 := by
  unfold actionGeneratedMatterCompleteFirstGermHessian
  exact canonicalCompleteMatterFirstGermHessian_eq_zero_iff _

/-- Faithful realization plus algebraic injectivity: the generated update is
the identity exactly on the complete action-residual zero fiber. -/
theorem actionGeneratedMatterCompleteFirstGermActual_eq_iff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedMatterCompleteFirstGermActual source configuration =
        configuration ↔
      matterCompleteDiracYukawaFirstGermResidual source configuration = 0 := by
  unfold actionGeneratedMatterCompleteFirstGermActual
  rw [installMatterCompleteFirstGermResponse_eq_iff,
    actionGeneratedMatterCompleteFirstGermHessian_eq_zero_iff]

theorem actionGeneratedMatterCompleteFirstGermActual_zeroFiber
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (residualZero :
      matterCompleteDiracYukawaFirstGermResidual source configuration = 0) :
    actionGeneratedMatterCompleteFirstGermActual source configuration =
      configuration :=
  (actionGeneratedMatterCompleteFirstGermActual_eq_iff source configuration).2
    residualZero

/-- Producer-soundness only: substitution of the action-generated Hessian
back into the same complete first-germ equation kills all four residual
components.  This is not counted as an independent EL closure. -/
theorem actionGeneratedMatterCompleteFirstGermActual_producerSound
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration) :
    matterCompleteDiracYukawaFirstGermResidual source
        (actionGeneratedMatterCompleteFirstGermActual source configuration) =
      0 := by
  funext direction
  apply matterCoordinateEquiv.injective
  rw [matterCompleteDiracYukawaFirstGermResidual_coordinate]
  unfold actionGeneratedMatterCompleteFirstGermActual
  rw [holonomicDiracYukawaCoordinateVector_install_completeFirstGerm
    source configuration smooth identityCoframe]
  have actionLaw :=
    canonicalCompleteMatterFirstGermHessian_producerSound
      (matterCompleteDiracYukawaFirstGermResidual source configuration)
      direction
  have coordinateActionLaw := congrArg matterCoordinateEquiv actionLaw
  simp only [map_add, map_zero] at coordinateActionLaw
  rw [matterCompleteDiracYukawaFirstGermResidual_coordinate]
    at coordinateActionLaw
  unfold actionGeneratedMatterCompleteFirstGermHessian
  rw [add_comm]
  simpa only [Pi.zero_apply, map_zero] using coordinateActionLaw

theorem actionGeneratedMatterCompleteFirstGermActual_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedMatterCompleteFirstGermActual source configuration).Smooth :=
  installMatterCompleteFirstGermResponse_smooth configuration smooth _

theorem actionGeneratedMatterCompleteFirstGermActual_nondegenerate
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedMatterCompleteFirstGermActual source configuration).Nondegenerate :=
  installMatterCompleteFirstGermResponse_nondegenerate configuration
    nondegenerate _

theorem actionGeneratedMatterCompleteFirstGermActual_matter_of_time_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeZero : point canonicalLorentzianTimeDirection = 0) :
    (actionGeneratedMatterCompleteFirstGermActual source configuration).matter
        point =
      configuration.matter point :=
  installMatterCompleteFirstGermResponse_matter_of_time_zero
    configuration _ point timeZero

@[simp] theorem actionGeneratedMatterCompleteFirstGermActual_matter_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedMatterCompleteFirstGermActual source configuration).matter 0 =
      configuration.matter 0 :=
  installMatterCompleteFirstGermResponse_matter_origin configuration _

theorem actionGeneratedMatterCompleteFirstGermActual_matter_firstJet_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((actionGeneratedMatterCompleteFirstGermActual source configuration).matter
            point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (configuration.matter point))
        0 direction :=
  installMatterCompleteFirstGermResponse_matter_firstJet_origin
    configuration smooth _ direction

theorem actionGeneratedMatterCompleteFirstGermActual_diracYukawa_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField
          (actionGeneratedMatterCompleteFirstGermActual source configuration)
          0) =
      generatedContinuumMatterVector source 0 0
        (toContinuumPointField configuration 0) :=
  generatedContinuumMatterVector_installMatterCompleteFirstGermResponse_origin
    source configuration smooth _

theorem actionGeneratedMatterCompleteFirstGermActual_diracYukawa_origin_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (baseZero :
      generatedContinuumMatterVector source 0 0
          (toContinuumPointField configuration 0) =
        0) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField
          (actionGeneratedMatterCompleteFirstGermActual source configuration)
          0) =
      0 := by
  rw [actionGeneratedMatterCompleteFirstGermActual_diracYukawa_origin
    source configuration smooth, baseZero]

end

end
  SaturationMonoid.PhysicsCore.StageNineMatterActionCompleteFirstGermResponse
