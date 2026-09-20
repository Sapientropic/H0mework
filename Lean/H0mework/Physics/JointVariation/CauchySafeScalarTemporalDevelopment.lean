import H0mework.Physics.SafeCauchy.FixedGlobalOperator
import H0mework.Physics.ScalarJets.FixedJointScalarSegmentRegularity
import H0mework.Physics.TimePrimitive.SecondAmbientJetRegularity
import H0mework.Physics.TimePrimitive.DiagonalHessian
import H0mework.Physics.DualVariation.ScalarEulerLocalLinearity
import H0mework.Physics.ScalarJets.ActionResponseOperatorCore

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment

open Filter
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveDiagonalHessian
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
open StageNineDiracDualFormNativeScalarEulerLocalLinearity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance scalarPrincipalProbeP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance scalarPrincipalProbeP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance scalarPrincipalProbeP286CoordinateNormedAddCommGroup :
    NormedAddCommGroup P286CoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : P286CoordinateIndex => ℝ)

local instance scalarPrincipalProbeP286CoordinateNormedSpace :
    NormedSpace ℝ P286CoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : P286CoordinateIndex => ℝ)

/-- The coefficient with which a coordinate-time scalar acceleration enters
the densitized temporal scalar momentum. -/
def scalarCoordinateTimePrincipalWeight
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : ℝ :=
  |Matrix.det (current.coframe point)| *
    coframeTemporalPrincipalScalar (current.coframe point)

theorem lorentzianMetricOfCoframe_inv_time_time_eq_neg_temporalPrincipalScalar
    (coframe : LorentzianCoframe) :
    (lorentzianMetricOfCoframe coframe)⁻¹ 0 0 =
      -coframeTemporalPrincipalScalar coframe := by
  have minkowskiInverse :
      minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
    apply Matrix.inv_eq_left_inv
    rw [minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num
  rw [lorentzianMetricOfCoframe, Matrix.mul_inv_rev,
    Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, minkowskiInverse]
  unfold minkowskiInternalMetric coframeTemporalPrincipalScalar
  simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiInternalSign]
  ring

theorem scalarCoordinateTimePrincipalWeight_ne_zero
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    scalarCoordinateTimePrincipalWeight current point ≠ 0 := by
  exact mul_ne_zero (abs_ne_zero.mpr nondegenerate) noncharacteristic

theorem scalarCoordinateTimePrincipalWeight_contDiffAt
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeRegular : ContDiffAt ℝ ∞ current.coframe point)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    ContDiffAt ℝ ∞ (scalarCoordinateTimePrincipalWeight current) point := by
  have volumeRegular : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (current.coframe candidate)|) point :=
    (coframe_volume_contDiffAt (current.coframe point) nondegenerate).comp
      point coframeRegular
  have inverseMetricRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (current.coframe candidate))⁻¹) point :=
    (lorentzianMetric_inv_contDiffAt (current.coframe point) nondegenerate).comp
      point coframeRegular
  have principalRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        coframeTemporalPrincipalScalar (current.coframe candidate)) point := by
    rw [show
      (fun candidate =>
        coframeTemporalPrincipalScalar (current.coframe candidate)) =
      fun candidate =>
        -((lorentzianMetricOfCoframe (current.coframe candidate))⁻¹ 0 0) by
      funext candidate
      rw [lorentzianMetricOfCoframe_inv_time_time_eq_neg_temporalPrincipalScalar]
      ring]
    exact
      (contDiffAt_pi.mp (contDiffAt_pi.mp inverseMetricRegular 0) 0).neg
  exact volumeRegular.mul principalRegular

/-- Pointwise complete-joint scalar acceleration normalized by the actual
coordinate-time kinetic principal of the same supplied current. -/
def completeJointCauchySafeScalarAccelerationProfile
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  (scalarCoordinateTimePrincipalWeight current point)⁻¹ •
    completeJointScalarAccelerationProfile source current point

theorem completeJointCauchySafeScalarAccelerationProfile_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (principalNonzero : scalarCoordinateTimePrincipalWeight current point ≠ 0) :
    ContDiffAt ℝ ∞
      (completeJointCauchySafeScalarAccelerationProfile source current) point := by
  have smoothCopy := smooth
  have coframeSmooth : ContDiff ℝ ∞ current.coframe :=
    holonomicCoframe_contDiff current smooth
  rcases smoothCopy with
    ⟨_coframeRegular, _gravityConnectionRegular, _gravityAuxiliaryRegular,
      _multiplierRegular, gaugeConnectionRegular, _gaugeAuxiliaryRegular,
      scalarRegular, matterRegular, _conjugateMatterRegular⟩
  have accelerationRegular : ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile source current) point :=
    completeJointScalarAccelerationProfile_contDiffAt_of_local
      source current point nondegenerate coframeSmooth.contDiffAt
      scalarRegular.contDiffAt matterRegular.contDiffAt
      (holonomicConjugateMatterCoordinates_contDiff current smooth).contDiffAt
      (fun direction => (gaugeConnectionRegular direction).contDiffAt)
  have inverseWeightRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (scalarCoordinateTimePrincipalWeight current candidate)⁻¹) point :=
    (scalarCoordinateTimePrincipalWeight_contDiffAt current point
      coframeSmooth.contDiffAt nondegenerate).inv principalNonzero
  unfold completeJointCauchySafeScalarAccelerationProfile
  exact inverseWeightRegular.smul accelerationRegular

theorem completeJointCauchySafeScalarAccelerationProfile_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiff ℝ ∞
      (completeJointCauchySafeScalarAccelerationProfile source current) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact completeJointCauchySafeScalarAccelerationProfile_contDiffAt
    source current smooth point (nondegenerate point)
    (scalarCoordinateTimePrincipalWeight_ne_zero current point
      (nondegenerate point) (noncharacteristic point))

/-- Complete temporal write with the matter and adjoint legs unchanged and
the scalar leg normalized by the same current's actual time principal. -/
def sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      source current with
    scalar := fun point =>
      current.scalar point +
        canonicalTimeSecondPrimitive
          (completeJointCauchySafeScalarAccelerationProfile source current)
          point }

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      source current).coframe = current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_gravityConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      source current).gravityConnection = current.gravityConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      source current).matter =
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        source current).matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      source current).conjugateMatter =
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        source current).conjugateMatter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalar_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      source current).scalar 0 = current.scalar 0 := by
  change current.scalar 0 +
      canonicalTimeSecondPrimitive
        (completeJointCauchySafeScalarAccelerationProfile source current) 0 =
    current.scalar 0
  rw [show (0 : BasePoint) = canonicalCauchySlicePoint 0 0 by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint]]
  simp

theorem completeJointCauchySafeScalarPrimitive_hasFDerivAt_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    HasFDerivAt
      (canonicalTimeSecondPrimitive
        (completeJointCauchySafeScalarAccelerationProfile source current))
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
  rw [show (0 : BasePoint) = canonicalCauchySlicePoint 0 0 by
    ext direction
    fin_cases direction <;> simp [canonicalCauchySlicePoint]]
  exact canonicalTimeSecondPrimitive_hasFDerivAt_zeroSlice_of_contDiff
    (completeJointCauchySafeScalarAccelerationProfile source current)
    (completeJointCauchySafeScalarAccelerationProfile_contDiff source current
      smooth nondegenerate noncharacteristic) 0

def completeJointCauchySafeScalarCovariantIncrement
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (formDirection : LorentzianIndex) : ScalarCoordinateCarrier :=
  let primitive := canonicalTimeSecondPrimitive
    (completeJointCauchySafeScalarAccelerationProfile source current)
  fieldDirectionalDerivative primitive point formDirection +
    scalarP286ActionBilinear
      (p286CoordinateEquiv (current.gaugeConnection point formDirection))
      (primitive point)

theorem completeJointCauchySafeScalarCovariantIncrement_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (formDirection : LorentzianIndex) :
    completeJointCauchySafeScalarCovariantIncrement source current 0
        formDirection = 0 := by
  let profile := completeJointCauchySafeScalarAccelerationProfile source current
  let primitive := canonicalTimeSecondPrimitive profile
  have primitiveDerivative : HasFDerivAt primitive
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
    simpa only [primitive, profile] using
      completeJointCauchySafeScalarPrimitive_hasFDerivAt_origin
        source current smooth nondegenerate noncharacteristic
  have primitiveOrigin : primitive 0 = 0 := by
    rw [show (0 : BasePoint) = canonicalCauchySlicePoint 0 0 by
      ext direction
      fin_cases direction <;> simp [canonicalCauchySlicePoint]]
    exact canonicalTimeSecondPrimitive_zeroSlice profile 0
  unfold completeJointCauchySafeScalarCovariantIncrement
  change fieldDirectionalDerivative primitive 0 formDirection +
      scalarP286ActionBilinear
        (p286CoordinateEquiv (current.gaugeConnection 0 formDirection))
        (primitive 0) = 0
  unfold fieldDirectionalDerivative
  rw [primitiveDerivative.fderiv, primitiveOrigin]
  simp

theorem completeJointCauchySafeScalarGaugeAction_hasFDerivAt_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (formDirection : LorentzianIndex) :
    HasFDerivAt
      (fun point =>
        scalarP286ActionBilinear
          (p286CoordinateEquiv (current.gaugeConnection point formDirection))
          (canonicalTimeSecondPrimitive
            (completeJointCauchySafeScalarAccelerationProfile source current)
            point))
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
  let profile := completeJointCauchySafeScalarAccelerationProfile source current
  let primitive := canonicalTimeSecondPrimitive profile
  let gaugeCoordinate := fun point =>
    p286CoordinateEquiv (current.gaugeConnection point formDirection)
  let outer := fun point =>
    scalarP286ActionBilinear.toContinuousBilinearMap (gaugeCoordinate point)
  have smoothCopy := smooth
  have gaugeRegular : ContDiff ℝ ∞ gaugeCoordinate := by
    rcases smoothCopy with
      ⟨_, _, _, _, gaugeConnectionRegular, _, _, _, _⟩
    exact gaugeConnectionRegular formDirection
  have outerContinuous : ContinuousAt outer 0 :=
    ((contDiff_const : ContDiff ℝ ∞
      (fun _ : BasePoint =>
        scalarP286ActionBilinear.toContinuousBilinearMap)).clm_apply
      gaugeRegular).continuous.continuousAt
  have primitiveDerivative : HasFDerivAt primitive
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
    simpa only [primitive, profile] using
      completeJointCauchySafeScalarPrimitive_hasFDerivAt_origin
        source current smooth nondegenerate noncharacteristic
  have primitiveOrigin : primitive 0 = 0 := by
    rw [show (0 : BasePoint) = canonicalCauchySlicePoint 0 0 by
      ext direction
      fin_cases direction <;> simp [canonicalCauchySlicePoint]]
    exact canonicalTimeSecondPrimitive_zeroSlice profile 0
  have primitiveQuotient :
      Tendsto (fun point => ‖point‖⁻¹ * ‖primitive point‖)
        (nhds 0) (nhds 0) := by
    simpa [primitiveOrigin] using
      (hasFDerivAt_iff_tendsto.mp primitiveDerivative)
  have upperTendsto :
      Tendsto
        (fun point => ‖outer point‖ * (‖point‖⁻¹ * ‖primitive point‖))
        (nhds 0) (nhds 0) := by
    simpa using outerContinuous.norm.tendsto.mul primitiveQuotient
  rw [hasFDerivAt_iff_tendsto]
  have productTendsto :
      Tendsto
        (fun point => ‖point‖⁻¹ * ‖outer point (primitive point)‖)
        (nhds 0) (nhds 0) := by
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun point =>
        mul_nonneg (inv_nonneg.mpr (norm_nonneg point)) (norm_nonneg _)) ?_
      upperTendsto
    filter_upwards [] with point
    calc
      ‖point‖⁻¹ * ‖outer point (primitive point)‖
          ≤ ‖point‖⁻¹ * (‖outer point‖ * ‖primitive point‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm (outer point) (primitive point))
          (inv_nonneg.mpr (norm_nonneg point))
      _ = ‖outer point‖ * (‖point‖⁻¹ * ‖primitive point‖) := by ring
  simp only [sub_zero, zero_apply]
  change Tendsto
    (fun point =>
      ‖point‖⁻¹ *
        ‖outer point (primitive point) - outer 0 (primitive 0)‖)
    (nhds 0) (nhds 0)
  simpa [primitiveOrigin] using productTendsto

theorem completeJointCauchySafeScalarCovariantIncrement_mixedDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (formDirection derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          completeJointCauchySafeScalarCovariantIncrement source current point
            formDirection)
        0 derivativeDirection =
      if formDirection = canonicalLorentzianTimeDirection ∧
          derivativeDirection = canonicalLorentzianTimeDirection then
        completeJointCauchySafeScalarAccelerationProfile source current 0
      else 0 := by
  let profile := completeJointCauchySafeScalarAccelerationProfile source current
  let primitive := canonicalTimeSecondPrimitive profile
  have profileRegular : ContDiff ℝ ∞ profile := by
    simpa only [profile] using
      completeJointCauchySafeScalarAccelerationProfile_contDiff source current
        smooth nondegenerate noncharacteristic
  have firstJetRegular : ContDiff ℝ 1 fun point =>
      fieldDirectionalDerivative primitive point formDirection := by
    unfold fieldDirectionalDerivative
    exact
      ((canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile
        profileRegular).fderiv_right (m := 1) (by norm_num)).clm_apply
          contDiff_const
  have gaugeActionDerivative : HasFDerivAt
      (fun point =>
        scalarP286ActionBilinear
          (p286CoordinateEquiv
            (current.gaugeConnection point formDirection))
          (primitive point))
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
    simpa only [primitive, profile] using
      completeJointCauchySafeScalarGaugeAction_hasFDerivAt_zero source current
        smooth nondegenerate noncharacteristic formDirection
  have firstJetDifferentiable : DifferentiableAt ℝ
      (fun point =>
        (fderiv ℝ primitive point) (coordinateDirection formDirection)) 0 := by
    simpa only [fieldDirectionalDerivative] using
      ((firstJetRegular.differentiable (by norm_num)).differentiableAt)
  unfold completeJointCauchySafeScalarCovariantIncrement
  change
    fieldDirectionalDerivative
      (fun point =>
        fieldDirectionalDerivative primitive point formDirection +
          scalarP286ActionBilinear
            (p286CoordinateEquiv
              (current.gaugeConnection point formDirection))
            (primitive point)) 0 derivativeDirection = _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstJetDifferentiable
    gaugeActionDerivative.differentiableAt,
    add_apply, gaugeActionDerivative.fderiv]
  change
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative primitive point formDirection)
        0 derivativeDirection + 0 = _
  have zeroPoint : canonicalCauchySlicePoint 0 0 = (0 : BasePoint) := by
    ext formDirection
    fin_cases formDirection <;> simp [canonicalCauchySlicePoint]
  have diagonal :=
    canonicalTimeSecondPrimitive_mixedSecondDerivative_zeroSlice_of_contDiff
      profile profileRegular 0 formDirection derivativeDirection
  simpa only [primitive, profile, zeroPoint, add_zero] using diagonal

theorem completeJointCauchySafeScalarCovariantIncrement_diagonalDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          completeJointCauchySafeScalarCovariantIncrement source current point
            direction)
        0 direction =
      if direction = canonicalLorentzianTimeDirection then
        completeJointCauchySafeScalarAccelerationProfile source current 0
      else 0 := by
  rw [completeJointCauchySafeScalarCovariantIncrement_mixedDerivative_origin
    source current smooth nondegenerate noncharacteristic direction direction]
  by_cases temporal : direction = canonicalLorentzianTimeDirection <;>
    simp [temporal]

theorem completeJointCauchySafeScalarCovariantIncrement_differentiableAt_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (formDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        completeJointCauchySafeScalarCovariantIncrement source current point
          formDirection) 0 := by
  let profile := completeJointCauchySafeScalarAccelerationProfile source current
  let primitive := canonicalTimeSecondPrimitive profile
  have profileRegular : ContDiff ℝ ∞ profile := by
    simpa only [profile] using
      completeJointCauchySafeScalarAccelerationProfile_contDiff source current
        smooth nondegenerate noncharacteristic
  have firstJetDifferentiable : DifferentiableAt ℝ
      (fun point => fieldDirectionalDerivative primitive point formDirection)
      0 := by
    unfold fieldDirectionalDerivative
    exact (((canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile
      profileRegular).fderiv_right (m := 1) (by norm_num)).clm_apply
        contDiff_const).differentiable (by norm_num) |>.differentiableAt
  have gaugeActionDifferentiable : DifferentiableAt ℝ
      (fun point =>
        scalarP286ActionBilinear
          (p286CoordinateEquiv
            (current.gaugeConnection point formDirection))
          (primitive point)) 0 := by
    exact (completeJointCauchySafeScalarGaugeAction_hasFDerivAt_zero
      source current smooth nondegenerate noncharacteristic formDirection
      ).differentiableAt
  unfold completeJointCauchySafeScalarCovariantIncrement
  exact firstJetDifferentiable.add gaugeActionDifferentiable

private theorem scalarP286ActionBilinear_coordinate_here
    (connection : P286LieBlockData)
    (scalar : ScalarCoordinateCarrier) :
    scalarP286ActionBilinear (p286CoordinateEquiv connection) scalar =
      scalarMotherLieAction (p286LieBlockEmbed connection) scalar := by
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm (p286CoordinateEquiv connection))) scalar =
      _
  rw [p286CoordinateEquiv.symm_apply_apply]

theorem
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalarCovariantDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (point : BasePoint) :
    holonomicScalarCovariantDerivative
        (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
          source current) point =
      holonomicScalarCovariantDerivative current point +
        completeJointCauchySafeScalarCovariantIncrement source current point := by
  let profile := completeJointCauchySafeScalarAccelerationProfile source current
  let primitive := canonicalTimeSecondPrimitive profile
  have profileRegular : ContDiff ℝ ∞ profile := by
    simpa only [profile] using
      completeJointCauchySafeScalarAccelerationProfile_contDiff source current
        smooth nondegenerate noncharacteristic
  have primitiveDifferentiable : DifferentiableAt ℝ primitive point :=
    (canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile profileRegular
      ).differentiable (by norm_num) |>.differentiableAt
  have currentScalarDifferentiable : DifferentiableAt ℝ current.scalar point := by
    rcases smooth with ⟨_, _, _, _, _, _, scalarRegular, _, _⟩
    exact (scalarRegular.differentiable (by norm_num)).differentiableAt
  funext formDirection
  unfold sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
    holonomicScalarCovariantDerivative
    completeJointCauchySafeScalarCovariantIncrement
  change
    fieldDirectionalDerivative
        (fun candidate => current.scalar candidate + primitive candidate)
        point formDirection +
      scalarMotherLieAction
        (p286LieBlockEmbed (current.gaugeConnection point formDirection))
        (current.scalar point + primitive point) =
      (fieldDirectionalDerivative current.scalar point formDirection +
        scalarMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection point formDirection))
          (current.scalar point)) +
        (fieldDirectionalDerivative primitive point formDirection +
          scalarP286ActionBilinear
            (p286CoordinateEquiv
              (current.gaugeConnection point formDirection))
            (primitive point))
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add currentScalarDifferentiable primitiveDifferentiable,
    add_apply, scalarMotherLieAction_add_right,
    scalarP286ActionBilinear_coordinate_here]
  abel

private def completeJointCauchySafeScalarMomentumIncrement
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) : ℝ :=
  let variation :=
    scalarVariationDifferentialDirection direction derivativeDirection
  let increment :=
    completeJointCauchySafeScalarCovariantIncrement source current
  generatedVolumeDensity (toContinuumPointField current point) *
    ((1 / 2 : ℝ) *
      ∑ first : LorentzianIndex,
        ∑ second : LorentzianIndex,
          ((lorentzianMetricOfCoframe (current.coframe point))⁻¹
              first second) *
            (scalarCoordinatePairingRe
                (variation first) (increment point second) +
              scalarCoordinatePairingRe
                (increment point first) (variation second)))

private theorem completeJointCauchySafe_scalarDifferentialMomentum_expansion
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source
        (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
          source current) direction derivativeDirection =
      scalarDifferentialMomentum source current direction derivativeDirection +
        completeJointCauchySafeScalarMomentumIncrement source current direction
          derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    completeJointCauchySafeScalarMomentumIncrement generatedVolumeDensity
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  rw [sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_coframe,
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalarCovariantDerivative
      source current smooth nondegenerate noncharacteristic]
  simp only [Pi.add_apply, scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  exact scalarWeightedDoubleSum_add_linear_scaled
    (abs (Matrix.det (current.coframe point))) (1 / 2)
    (fun first second =>
      (lorentzianMetricOfCoframe (current.coframe point))⁻¹ first second)
    (fun first second =>
      scalarCoordinatePairingRe
        (scalarVariationDifferentialDirection direction derivativeDirection
          first)
        (holonomicScalarCovariantDerivative current point second))
    (fun first second =>
      scalarCoordinatePairingRe
        (holonomicScalarCovariantDerivative current point first)
        (scalarVariationDifferentialDirection direction derivativeDirection
          second))
    (fun first second =>
      scalarCoordinatePairingRe
        (scalarVariationDifferentialDirection direction derivativeDirection
          first)
        (completeJointCauchySafeScalarCovariantIncrement source current point
          second))
    (fun first second =>
      scalarCoordinatePairingRe
        (completeJointCauchySafeScalarCovariantIncrement source current point
          first)
        (scalarVariationDifferentialDirection direction derivativeDirection
          second))

private theorem fieldDirectionalDerivative_finset_sum_real_at_origin
    {Index : Type*} [Fintype Index]
    (field : Index → BasePoint → ℝ)
    (fieldDifferentiable : ∀ index, DifferentiableAt ℝ (field index) 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => ∑ index, field index point)
        0 direction =
      ∑ index, fieldDirectionalDerivative (field index) 0 direction := by
  have derivative : HasFDerivAt
      (∑ index, field index)
      (∑ index, fderiv ℝ (field index) 0) 0 :=
    HasFDerivAt.sum (u := Finset.univ) fun index _ =>
      (fieldDifferentiable index).hasFDerivAt
  have pointwise : HasFDerivAt
      (fun point => ∑ index, field index point)
      (∑ index, fderiv ℝ (field index) 0) 0 := by
    convert derivative using 1
    funext point
    simp
  unfold fieldDirectionalDerivative
  rw [pointwise.fderiv]
  simp

private theorem fieldDirectionalDerivative_add_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

private theorem fieldDirectionalDerivative_mul_of_right_zero_at_origin
    (left right : BasePoint → ℝ)
    (leftDifferentiable : DifferentiableAt ℝ left 0)
    (rightDifferentiable : DifferentiableAt ℝ right 0)
    (rightZero : right 0 = 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => left point * right point)
        0 direction =
      left 0 * fieldDirectionalDerivative right 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_mul leftDifferentiable rightDifferentiable]
  simp [rightZero]

private theorem scalarPairingLeft_directionalDerivative_at_origin
    (field : BasePoint → ScalarCoordinateCarrier)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (fixed : ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => scalarCoordinatePairingRe fixed (field point))
        0 direction =
      scalarCoordinatePairingRe fixed
        (fieldDirectionalDerivative field 0 direction) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap fixed
  have derivative := pairing.hasFDerivAt.comp 0
    fieldDifferentiable.hasFDerivAt
  change fieldDirectionalDerivative (fun point => pairing (field point))
      0 direction = pairing (fieldDirectionalDerivative field 0 direction)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing (field point)) = pairing ∘ field by rfl,
    derivative.fderiv]
  rfl

private theorem scalarPairingRight_directionalDerivative_at_origin
    (field : BasePoint → ScalarCoordinateCarrier)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (fixed : ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => scalarCoordinatePairingRe (field point) fixed)
        0 direction =
      scalarCoordinatePairingRe
        (fieldDirectionalDerivative field 0 direction) fixed := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip fixed
  have derivative := pairing.hasFDerivAt.comp 0
    fieldDifferentiable.hasFDerivAt
  change fieldDirectionalDerivative (fun point => pairing (field point))
      0 direction = pairing (fieldDirectionalDerivative field 0 direction)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing (field point)) = pairing ∘ field by rfl,
    derivative.fderiv]
  rfl

private theorem scalarCoordinatePairingRe_comm_here
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second =
      scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re, mul_comm]

private theorem scalarCoordinatePairingRe_zero_left_here
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe 0 value = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_zero_right_here
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe value 0 = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem completeJointCauchySafeScalarMomentumIncrement_diagonalDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (completeJointCauchySafeScalarMomentumIncrement source current direction
          derivativeDirection)
        0 derivativeDirection =
      if derivativeDirection = canonicalLorentzianTimeDirection then
        -scalarCoordinateTimePrincipalWeight current 0 *
          scalarCoordinatePairingRe direction
            (completeJointCauchySafeScalarAccelerationProfile source current 0)
      else 0 := by
  let variation :=
    scalarVariationDifferentialDirection direction derivativeDirection
  let increment :=
    completeJointCauchySafeScalarCovariantIncrement source current
  let volume := fun point => |Matrix.det (current.coframe point)|
  let metric := fun point first second =>
    (lorentzianMetricOfCoframe (current.coframe point))⁻¹ first second
  let pairingTerm := fun first second point =>
    scalarCoordinatePairingRe (variation first) (increment point second) +
      scalarCoordinatePairingRe (increment point first) (variation second)
  let weightedTerm := fun first second point =>
    metric point first second * pairingTerm first second point
  let doubleSum := fun point =>
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex, weightedTerm first second point
  let kinetic := fun point => (1 / 2 : ℝ) * doubleSum point
  have coframeRegular : ContDiff ℝ ∞ current.coframe :=
    holonomicCoframe_contDiff current smooth
  have volumeRegular : ContDiffAt ℝ ∞ volume 0 := by
    exact (coframe_volume_contDiffAt (current.coframe 0)
      (nondegenerate 0)).comp 0 coframeRegular.contDiffAt
  have metricRegular : ContDiffAt ℝ ∞
      (fun point => (lorentzianMetricOfCoframe (current.coframe point))⁻¹)
      0 := by
    exact (lorentzianMetric_inv_contDiffAt (current.coframe 0)
      (nondegenerate 0)).comp 0 coframeRegular.contDiffAt
  have metricEntryDifferentiable (first second : LorentzianIndex) :
      DifferentiableAt ℝ (fun point => metric point first second) 0 :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp metricRegular first) second
      ).differentiableAt (by norm_num)
  have incrementDifferentiable (formDirection : LorentzianIndex) :
      DifferentiableAt ℝ (fun point => increment point formDirection) 0 := by
    simpa only [increment] using
      completeJointCauchySafeScalarCovariantIncrement_differentiableAt_origin
        source current smooth nondegenerate noncharacteristic formDirection
  have incrementOrigin (formDirection : LorentzianIndex) :
      increment 0 formDirection = 0 := by
    simpa only [increment] using
      completeJointCauchySafeScalarCovariantIncrement_origin source current
        smooth nondegenerate noncharacteristic formDirection
  have pairingTermDifferentiable (first second : LorentzianIndex) :
      DifferentiableAt ℝ (pairingTerm first second) 0 := by
    let leftPairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap
        (variation first)
    let rightPairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip
        (variation second)
    exact
      (leftPairing.hasFDerivAt.comp 0
        (incrementDifferentiable second).hasFDerivAt).differentiableAt.add
      (rightPairing.hasFDerivAt.comp 0
        (incrementDifferentiable first).hasFDerivAt).differentiableAt
  have pairingTermOrigin (first second : LorentzianIndex) :
      pairingTerm first second 0 = 0 := by
    simp [pairingTerm, incrementOrigin,
      scalarCoordinatePairingRe_zero_left_here,
      scalarCoordinatePairingRe_zero_right_here]
  have pairingTermDerivative (first second : LorentzianIndex) :
      fieldDirectionalDerivative (pairingTerm first second) 0
          derivativeDirection =
        scalarCoordinatePairingRe (variation first)
            (fieldDirectionalDerivative
              (fun point => increment point second) 0 derivativeDirection) +
          scalarCoordinatePairingRe
          (fieldDirectionalDerivative
              (fun point => increment point first) 0 derivativeDirection)
            (variation second) := by
    unfold pairingTerm
    have leftDifferentiable : DifferentiableAt ℝ
        (fun point => scalarCoordinatePairingRe
          (variation first) (increment point second)) 0 :=
      ((scalarCoordinatePairingReBilinear.toContinuousBilinearMap
        (variation first)).hasFDerivAt.comp 0
          (incrementDifferentiable second).hasFDerivAt).differentiableAt
    have rightDifferentiable : DifferentiableAt ℝ
        (fun point => scalarCoordinatePairingRe
          (increment point first) (variation second)) 0 :=
      ((scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip
        (variation second)).hasFDerivAt.comp 0
          (incrementDifferentiable first).hasFDerivAt).differentiableAt
    calc
      fieldDirectionalDerivative
          (fun point =>
            scalarCoordinatePairingRe (variation first)
                (increment point second) +
              scalarCoordinatePairingRe (increment point first)
                (variation second))
          0 derivativeDirection =
        fieldDirectionalDerivative
            (fun point => scalarCoordinatePairingRe
              (variation first) (increment point second))
            0 derivativeDirection +
          fieldDirectionalDerivative
            (fun point => scalarCoordinatePairingRe
              (increment point first) (variation second))
            0 derivativeDirection :=
        fieldDirectionalDerivative_add_real_at_origin _ _
          leftDifferentiable rightDifferentiable derivativeDirection
      _ = _ := by
        rw [scalarPairingLeft_directionalDerivative_at_origin
          (fun point => increment point second) (incrementDifferentiable second)
          (variation first) derivativeDirection,
          scalarPairingRight_directionalDerivative_at_origin
            (fun point => increment point first) (incrementDifferentiable first)
            (variation second) derivativeDirection]
  have weightedTermDifferentiable (first second : LorentzianIndex) :
      DifferentiableAt ℝ (weightedTerm first second) 0 :=
    (metricEntryDifferentiable first second).mul
      (pairingTermDifferentiable first second)
  have weightedTermDerivative (first second : LorentzianIndex) :
      fieldDirectionalDerivative (weightedTerm first second) 0
          derivativeDirection =
        metric 0 first second *
          (scalarCoordinatePairingRe (variation first)
              (fieldDirectionalDerivative
                (fun point => increment point second) 0
                derivativeDirection) +
            scalarCoordinatePairingRe
              (fieldDirectionalDerivative
                (fun point => increment point first) 0
                derivativeDirection)
              (variation second)) := by
    unfold weightedTerm
    rw [fieldDirectionalDerivative_mul_of_right_zero_at_origin
      (fun point => metric point first second)
      (pairingTerm first second)
      (metricEntryDifferentiable first second)
      (pairingTermDifferentiable first second)
      (pairingTermOrigin first second) derivativeDirection,
      pairingTermDerivative first second]
  have doubleSumDifferentiable : DifferentiableAt ℝ doubleSum 0 := by
    unfold doubleSum
    fun_prop
  have doubleSumDerivativeFormula :
      fieldDirectionalDerivative doubleSum 0 derivativeDirection =
        ∑ first : LorentzianIndex,
          ∑ second : LorentzianIndex,
            metric 0 first second *
              (scalarCoordinatePairingRe (variation first)
                  (fieldDirectionalDerivative
                    (fun point => increment point second) 0
                    derivativeDirection) +
                scalarCoordinatePairingRe
                  (fieldDirectionalDerivative
                    (fun point => increment point first) 0
                    derivativeDirection)
                  (variation second)) := by
    unfold doubleSum
    rw [fieldDirectionalDerivative_finset_sum_real_at_origin
      (fun first point =>
        ∑ second : LorentzianIndex, weightedTerm first second point)
      (fun first => by fun_prop) derivativeDirection]
    apply Finset.sum_congr rfl
    intro first _
    rw [fieldDirectionalDerivative_finset_sum_real_at_origin
      (fun second => weightedTerm first second)
      (fun second => weightedTermDifferentiable first second)
      derivativeDirection]
    apply Finset.sum_congr rfl
    intro second _
    exact weightedTermDerivative first second
  have doubleSumDerivative :
      fieldDirectionalDerivative doubleSum 0 derivativeDirection =
        if derivativeDirection = canonicalLorentzianTimeDirection then
          2 * metric 0 canonicalLorentzianTimeDirection
              canonicalLorentzianTimeDirection *
            scalarCoordinatePairingRe direction
              (completeJointCauchySafeScalarAccelerationProfile
                source current 0)
        else 0 := by
    rw [doubleSumDerivativeFormula]
    simp_rw [show ∀ formDirection,
        fieldDirectionalDerivative
            (fun point => increment point formDirection) 0
            derivativeDirection =
          if formDirection = canonicalLorentzianTimeDirection ∧
              derivativeDirection = canonicalLorentzianTimeDirection then
            completeJointCauchySafeScalarAccelerationProfile source current 0
          else 0 by
      intro formDirection
      simpa only [increment] using
        completeJointCauchySafeScalarCovariantIncrement_mixedDerivative_origin
          source current smooth nondegenerate noncharacteristic formDirection
            derivativeDirection]
    fin_cases derivativeDirection <;>
      simp [variation, scalarVariationDifferentialDirection,
        canonicalLorentzianTimeDirection, Fin.sum_univ_four,
        scalarCoordinatePairingRe_zero_left_here,
        scalarCoordinatePairingRe_zero_right_here,
        scalarCoordinatePairingRe_comm_here] ;
      ring
  have doubleSumOrigin : doubleSum 0 = 0 := by
    simp [doubleSum, weightedTerm, pairingTermOrigin]
  have kineticDifferentiable : DifferentiableAt ℝ kinetic 0 := by
    unfold kinetic
    fun_prop
  have kineticOrigin : kinetic 0 = 0 := by
    simp [kinetic, doubleSumOrigin]
  have kineticDerivative :
      fieldDirectionalDerivative kinetic 0 derivativeDirection =
        (1 / 2 : ℝ) *
          fieldDirectionalDerivative doubleSum 0 derivativeDirection := by
    unfold kinetic fieldDirectionalDerivative
    rw [fderiv_const_mul doubleSumDifferentiable (1 / 2 : ℝ)]
    rfl
  have momentumEquality :
      completeJointCauchySafeScalarMomentumIncrement source current direction
          derivativeDirection =
        fun point => volume point * kinetic point := by
    funext point
    unfold completeJointCauchySafeScalarMomentumIncrement volume kinetic
      doubleSum weightedTerm pairingTerm metric variation increment
      generatedVolumeDensity
    simp only [toContinuumPointField]
  rw [momentumEquality,
    fieldDirectionalDerivative_mul_of_right_zero_at_origin volume kinetic
      (volumeRegular.differentiableAt (by norm_num)) kineticDifferentiable
      kineticOrigin derivativeDirection,
    kineticDerivative, doubleSumDerivative]
  by_cases temporal :
      derivativeDirection = canonicalLorentzianTimeDirection
  · subst derivativeDirection
    unfold volume metric scalarCoordinateTimePrincipalWeight
    simp only [canonicalLorentzianTimeDirection]
    rw [lorentzianMetricOfCoframe_inv_time_time_eq_neg_temporalPrincipalScalar]
    simp only [if_true]
    ring
  · simp [temporal]

private theorem
    completeJointCauchySafeScalarMomentumIncrement_differentiableAt_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (completeJointCauchySafeScalarMomentumIncrement source current direction
        derivativeDirection) 0 := by
  let variation :=
    scalarVariationDifferentialDirection direction derivativeDirection
  let increment :=
    completeJointCauchySafeScalarCovariantIncrement source current
  let volume := fun point => |Matrix.det (current.coframe point)|
  let metric := fun point first second =>
    (lorentzianMetricOfCoframe (current.coframe point))⁻¹ first second
  let pairingTerm := fun first second point =>
    scalarCoordinatePairingRe (variation first) (increment point second) +
      scalarCoordinatePairingRe (increment point first) (variation second)
  let weightedTerm := fun first second point =>
    metric point first second * pairingTerm first second point
  let doubleSum := fun point =>
    ∑ first : LorentzianIndex,
      ∑ second : LorentzianIndex, weightedTerm first second point
  have volumeDifferentiable : DifferentiableAt ℝ volume 0 :=
    ((scalarHolonomicGeneratedVolumeDensity_contDiff current smooth
      nondegenerate).differentiable (by norm_num)).differentiableAt
  have metricRegular : ContDiff ℝ ∞
      (fun point => (lorentzianMetricOfCoframe (current.coframe point))⁻¹) :=
    holonomicLorentzianMetric_inv_contDiff current smooth nondegenerate
  have metricEntryDifferentiable (first second : LorentzianIndex) :
      DifferentiableAt ℝ (fun point => metric point first second) 0 :=
    ((contDiff_pi.mp (contDiff_pi.mp metricRegular first) second
      ).differentiable (by norm_num)).differentiableAt
  have incrementDifferentiable (formDirection : LorentzianIndex) :
      DifferentiableAt ℝ (fun point => increment point formDirection) 0 := by
    simpa only [increment] using
      completeJointCauchySafeScalarCovariantIncrement_differentiableAt_origin
        source current smooth nondegenerate noncharacteristic formDirection
  have pairingTermDifferentiable (first second : LorentzianIndex) :
      DifferentiableAt ℝ (pairingTerm first second) 0 := by
    let leftPairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap
        (variation first)
    let rightPairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip
        (variation second)
    exact
      (leftPairing.hasFDerivAt.comp 0
        (incrementDifferentiable second).hasFDerivAt).differentiableAt.add
      (rightPairing.hasFDerivAt.comp 0
        (incrementDifferentiable first).hasFDerivAt).differentiableAt
  have weightedTermDifferentiable (first second : LorentzianIndex) :
      DifferentiableAt ℝ (weightedTerm first second) 0 :=
    (metricEntryDifferentiable first second).mul
      (pairingTermDifferentiable first second)
  have doubleSumDifferentiable : DifferentiableAt ℝ doubleSum 0 := by
    unfold doubleSum
    fun_prop
  have momentumEquality :
      completeJointCauchySafeScalarMomentumIncrement source current direction
          derivativeDirection =
        fun point => volume point * ((1 / 2 : ℝ) * doubleSum point) := by
    funext point
    unfold completeJointCauchySafeScalarMomentumIncrement volume doubleSum
      weightedTerm pairingTerm metric variation increment
      generatedVolumeDensity
    simp only [toContinuumPointField]
  rw [momentumEquality]
  exact volumeDifferentiable.mul
    (doubleSumDifferentiable.const_mul (1 / 2 : ℝ))

private theorem completeJointCauchySafeScalarDivergence_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence source
        (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
          source current)
        direction 0 =
      scalarDifferentialMomentumDivergence source current direction 0 -
        scalarCoordinateTimePrincipalWeight current 0 *
          scalarCoordinatePairingRe direction
            (completeJointCauchySafeScalarAccelerationProfile source current 0) := by
  unfold scalarDifferentialMomentumDivergence
  have derivativeExpansion (derivativeDirection : LorentzianIndex) :
      fieldDirectionalDerivative
          (scalarDifferentialMomentum source
            (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
              source current)
            direction derivativeDirection)
          0 derivativeDirection =
        fieldDirectionalDerivative
            (scalarDifferentialMomentum source current direction
              derivativeDirection)
            0 derivativeDirection +
          fieldDirectionalDerivative
            (completeJointCauchySafeScalarMomentumIncrement source current
              direction derivativeDirection)
            0 derivativeDirection := by
    rw [completeJointCauchySafe_scalarDifferentialMomentum_expansion source
      current smooth nondegenerate noncharacteristic direction
      derivativeDirection]
    exact fieldDirectionalDerivative_add_real_at_origin _ _
      ((scalarDifferentialMomentum_contDiff source current smooth
        nondegenerate direction derivativeDirection).differentiable
          (by norm_num)).differentiableAt
      (completeJointCauchySafeScalarMomentumIncrement_differentiableAt_origin
        source current smooth nondegenerate noncharacteristic direction
          derivativeDirection)
      derivativeDirection
  simp_rw [derivativeExpansion]
  rw [Finset.sum_add_distrib]
  simp_rw [completeJointCauchySafeScalarMomentumIncrement_diagonalDerivative_origin
    source current smooth nondegenerate noncharacteristic direction]
  simp [Fin.sum_univ_four, canonicalLorentzianTimeDirection]
  ring

private theorem completeJointCauchySafeScalarAlgebraic_origin_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
          source current)
        direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient source current direction
        0 := by
  let output :=
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      source current
  have coframeEquality : output.coframe = current.coframe := rfl
  have gaugeConnectionEquality :
      output.gaugeConnection = current.gaugeConnection := rfl
  have scalarEquality : output.scalar 0 = current.scalar 0 := by
    simpa only [output] using
      sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalar_origin
        source current
  have matterEquality : output.matter 0 = current.matter 0 := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        source current).matter 0 = current.matter 0
    rw [show (0 : BasePoint) = canonicalCauchySlicePoint 0 0 by
      ext formDirection
      fin_cases formDirection <;> simp [canonicalCauchySlicePoint]]
    exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        source current 0
  have conjugateMatterEquality :
      output.conjugateMatter 0 = current.conjugateMatter 0 := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        source current).conjugateMatter 0 = current.conjugateMatter 0
    rw [show (0 : BasePoint) = canonicalCauchySlicePoint 0 0 by
      ext formDirection
      fin_cases formDirection <;> simp [canonicalCauchySlicePoint]]
    exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        source current 0
  have incrementZero :
      completeJointCauchySafeScalarCovariantIncrement source current 0 = 0 := by
    funext formDirection
    exact completeJointCauchySafeScalarCovariantIncrement_origin source current
      smooth nondegenerate noncharacteristic formDirection
  have scalarCovariantEquality :
      holonomicScalarCovariantDerivative output 0 =
        holonomicScalarCovariantDerivative current 0 := by
    simpa only [output, incrementZero, add_zero] using
      sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalarCovariantDerivative
        source current smooth nondegenerate noncharacteristic 0
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [coframeEquality, scalarCovariantEquality, gaugeConnectionEquality,
    scalarEquality, matterEquality, conjugateMatterEquality]

theorem completeJointCauchySafeScalarAccelerationProfile_actionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (point : BasePoint)
    (principalNonzero : scalarCoordinateTimePrincipalWeight current point ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source current direction
        point =
      -scalarCoordinateTimePrincipalWeight current point *
        scalarCoordinatePairingRe direction
          (completeJointCauchySafeScalarAccelerationProfile
            source current point) := by
  have coframeSmooth : ContDiff ℝ ∞ current.coframe :=
    holonomicCoframe_contDiff current smooth
  rcases smooth with
    ⟨coframeRegular, _gravityConnectionRegular, _gravityAuxiliaryRegular,
      _multiplierRegular, gaugeConnectionRegular, _gaugeAuxiliaryRegular,
      scalarRegular, _matterRegular, _conjugateMatterRegular⟩
  let eulerDual : Module.Dual ℝ ScalarCoordinateCarrier :=
    { toFun := fun candidate =>
        diracDualScalarEulerLagrangeDirectionalCoefficient source current
          candidate point
      map_add' := fun first second =>
        diracDualScalarEulerLagrangeDirectionalCoefficient_add_of_local
          source current point (nondegenerate point)
          coframeSmooth.contDiffAt
          scalarRegular.contDiffAt
          (fun formDirection => (gaugeConnectionRegular formDirection).contDiffAt)
          first second
      map_smul' := fun parameter candidate => by
        simpa only [RingHom.id_apply, smul_eq_mul] using
          diracDualScalarEulerLagrangeDirectionalCoefficient_real_smul_of_local
            source current point (nondegenerate point)
            coframeSmooth.contDiffAt
            scalarRegular.contDiffAt
            (fun formDirection =>
              (gaugeConnectionRegular formDirection).contDiffAt)
            parameter candidate }
  have accelerationEq :
      completeJointScalarAccelerationProfile source current point =
        -scalarActionRealDual eulerDual := by
    unfold completeJointScalarAccelerationProfile
    change
      genericDiracDualScalarGeneratedAcceleration source
          (completeJointRepairedConstitutiveCurrent source
            (completeJointGeneratedProfileRestartCurrent source current point)) =
        -scalarActionRealDual eulerDual
    unfold genericDiracDualScalarGeneratedAcceleration scalarActionRealDual
    congr 1
    apply PiLp.ext
    intro index
    change
      ((genericDiracDualScalarTemporalDemandDual source
            (completeJointRepairedConstitutiveCurrent source
              (completeJointGeneratedProfileRestartCurrent source current point))
            (scalarRealBasis index) : ℂ) +
        (genericDiracDualScalarTemporalDemandDual source
            (completeJointRepairedConstitutiveCurrent source
              (completeJointGeneratedProfileRestartCurrent source current point))
            (scalarImaginaryBasis index) : ℂ) * Complex.I) =
      (((eulerDual (scalarRealBasis index) : ℂ) +
        (eulerDual (scalarImaginaryBasis index) : ℂ) * Complex.I))
    rw [genericDiracDualScalarTemporalDemandDual_realBasis,
      genericDiracDualScalarTemporalDemandDual_imaginaryBasis,
      completeJointScalarRawTemporalDemand_eq_currentScalarEuler,
      completeJointScalarRawTemporalDemand_eq_currentScalarEuler]
    rfl
  rw [completeJointCauchySafeScalarAccelerationProfile, accelerationEq,
    scalarCoordinatePairingRe_real_smul_right]
  change eulerDual direction = _
  rw [show scalarCoordinatePairingRe direction (-scalarActionRealDual eulerDual) =
      -eulerDual direction by
    rw [show -scalarActionRealDual eulerDual =
        (-1 : ℝ) • scalarActionRealDual eulerDual by simp,
      scalarCoordinatePairingRe_real_smul_right,
      scalarCoordinatePairingRe_actionRealDual]
    ring]
  field_simp [principalNonzero]

theorem
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalarEuler_origin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
          source current)
        direction 0 = 0 := by
  have actionLaw :=
    completeJointCauchySafeScalarAccelerationProfile_actionLaw source current
      smooth nondegenerate 0
      (scalarCoordinateTimePrincipalWeight_ne_zero current 0
        (nondegenerate 0) (noncharacteristic 0)) direction
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient at actionLaw ⊢
  rw [completeJointCauchySafeScalarAlgebraic_origin_eq_current source current
      smooth nondegenerate noncharacteristic direction,
    completeJointCauchySafeScalarDivergence_origin source current smooth
      nondegenerate noncharacteristic direction]
  calc
    diracDualScalarAlgebraicDirectionalCoefficient source current direction 0 -
          (scalarDifferentialMomentumDivergence source current direction 0 -
            scalarCoordinateTimePrincipalWeight current 0 *
              scalarCoordinatePairingRe direction
                (completeJointCauchySafeScalarAccelerationProfile source current
                  0)) =
        (diracDualScalarAlgebraicDirectionalCoefficient source current direction
            0 -
          scalarDifferentialMomentumDivergence source current direction 0) +
          scalarCoordinateTimePrincipalWeight current 0 *
            scalarCoordinatePairingRe direction
              (completeJointCauchySafeScalarAccelerationProfile source current
                0) := by ring
    _ = 0 := by rw [actionLaw]; ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
