import H0mework.Physics.JointVariation.CauchySafeScalarTemporalDevelopment
import H0mework.Physics.Cauchy.P286ConnectionRelativeScalarCauchyDevelopmentOperator
import H0mework.Physics.Exterior.ScalarActionTemporalMomentumLegendreVelocity
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance

/-!
# Connection-relative scalar normal-constraint Cauchy development

For a non-identity Cauchy-safe coframe, setting the coordinate derivative
`D₀ φ` to zero does not in general kill the scalar temporal momentum:
the inverse metric mixes the coordinate-time row with the spatial rows.

This module constructs the unique connection-relative affine Cauchy velocity
whose *normal* scalar momentum vanishes:

```text
q(e) D₀φ = Σᵢ g⁰ⁱ Dᵢφ,
q(e) = -g⁰⁰.
```

The writer reads only the supplied current, its coframe, scalar first jet and
P286 connection.  It accepts no desired velocity, momentum zero, Gauss zero,
residual, branch, target field, or equation receipt.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ConnectionRelativeScalarCauchyDevelopmentOperator
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionTemporalMomentumLegendreVelocity
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance normalConstraintP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance normalConstraintP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance normalConstraintP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Canonical normal velocity -/

/-- Spatial inverse-metric contraction of the supplied scalar covariant
first jet along the coordinate-time row. -/
def scalarNormalConstraintSpatialDemand
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  ∑ axis : Fin 3,
    (((lorentzianMetricOfCoframe (current.coframe point))⁻¹) 0 axis.succ) •
      holonomicScalarCovariantDerivative current point axis.succ

/-- The unique covariant coordinate-time velocity that makes the complete
inverse-metric time row vanish.  The inverse is a total formula; its
noncharacteristic qualification is used only by the correctness theorem. -/
def scalarNormalConstraintCovariantVelocity
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  (coframeTemporalPrincipalScalar (current.coframe point))⁻¹ •
    scalarNormalConstraintSpatialDemand current point

/-- Raw coordinate derivative installed on the zero slice.  Subtracting the
actual P286 connection action converts the generated raw derivative into the
covariant velocity above. -/
def scalarNormalConstraintRawVelocity
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) : ScalarCoordinateCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  scalarNormalConstraintCovariantVelocity current point -
    scalarMotherLieAction
      (p286LieBlockEmbed
        (current.gaugeConnection point canonicalLorentzianTimeDirection))
      (current.scalar point)

/-- Canonical affine realization of the generated normal-constraint Cauchy
data.  Every non-scalar primitive field is inherited literally. -/
def p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    scalar := fun point =>
      current.scalar
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) +
        canonicalTimeProjection point •
          scalarNormalConstraintRawVelocity current
            (canonicalSpatialProjection point) }

@[simp] theorem normalConstraint_coframe
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).coframe = current.coframe :=
  rfl

@[simp] theorem normalConstraint_gravityConnection
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).gravityConnection = current.gravityConnection :=
  rfl

@[simp] theorem normalConstraint_gravityAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).gravityAuxiliary = current.gravityAuxiliary :=
  rfl

@[simp] theorem normalConstraint_gravitySimplicityMultiplier
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).gravitySimplicityMultiplier =
        current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem normalConstraint_gaugeConnection
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem normalConstraint_gaugeAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).gaugeAuxiliary = current.gaugeAuxiliary :=
  rfl

@[simp] theorem normalConstraint_matter
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).matter = current.matter :=
  rfl

@[simp] theorem normalConstraint_conjugateMatter
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).conjugateMatter = current.conjugateMatter :=
  rfl

@[simp] theorem normalConstraint_scalar_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).scalar (canonicalCauchySlicePoint 0 space) =
        current.scalar (canonicalCauchySlicePoint 0 space) := by
  simp [p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator]

/-! ## Generated first jet -/

theorem normalConstraint_scalar_timeLine_hasDerivAt
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) (time : ℝ) :
    NormedHasDerivAt
      (fun candidateTime =>
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current).scalar (canonicalCauchySlicePoint candidateTime space))
      (scalarNormalConstraintRawVelocity current space) time := by
  have generated : NormedHasDerivAt
      (fun candidateTime =>
        current.scalar (canonicalCauchySlicePoint 0 space) +
          candidateTime • scalarNormalConstraintRawVelocity current space)
      (scalarNormalConstraintRawVelocity current space) time := by
    change NormedHasDerivAt
      ((fun _ : ℝ => current.scalar (canonicalCauchySlicePoint 0 space)) +
        fun candidateTime =>
          candidateTime • scalarNormalConstraintRawVelocity current space)
      (scalarNormalConstraintRawVelocity current space) time
    simpa only [id_eq, zero_add, one_smul] using
      (hasDerivAt_const time
        (current.scalar (canonicalCauchySlicePoint 0 space))).add
        ((hasDerivAt_id time).smul_const
          (scalarNormalConstraintRawVelocity current space))
  simpa [p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator]
    using generated

theorem normalConstraint_scalar_temporalDerivative_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (generatedDifferentiable : DifferentiableAt ℝ
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
        current).scalar
      (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current).scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      scalarNormalConstraintRawVelocity current space := by
  have ambient := field_timeLine_hasDerivAt
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).scalar space 0 generatedDifferentiable
  have generated := normalConstraint_scalar_timeLine_hasDerivAt current space 0
  simpa using ambient.unique generated

theorem normalConstraint_scalar_spatialDerivative_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) (axis : Fin 3)
    (currentDifferentiable : DifferentiableAt ℝ current.scalar
      (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable : DifferentiableAt ℝ
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
        current).scalar
      (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current).scalar
        (canonicalCauchySlicePoint 0 space) axis.succ =
      fieldDirectionalDerivative current.scalar
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  have generatedSliceDerivative :=
    generatedDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  have currentSliceDerivative :=
    currentDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  have sliceEquality :
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current).scalar ∘ canonicalCauchySlicePoint 0 =
        current.scalar ∘ canonicalCauchySlicePoint 0 := by
    funext candidateSpace
    exact normalConstraint_scalar_zeroSlice current candidateSpace
  have fderivEquality := congrArg (fun field => fderiv ℝ field space)
    sliceEquality
  rw [generatedSliceDerivative.fderiv, currentSliceDerivative.fderiv]
    at fderivEquality
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] ScalarCoordinateCarrier =>
      derivative (canonicalSpatialCoordinateDirection axis))
    fderivEquality
  unfold fieldDirectionalDerivative
  simpa only [ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using applied

/-! ## Global regularity of the generated writer -/

private theorem zeroSliceProjection_contDiff :
    ContDiff ℝ ∞ (fun point : BasePoint =>
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) := by
  have zeroSlice : ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext space
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
      simp]
    exact canonicalSpatialInclusion.contDiff
  exact zeroSlice.comp canonicalSpatialProjection.contDiff

private theorem inverseMetric_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    ContDiff ℝ ∞ (fun point =>
      (lorentzianMetricOfCoframe (current.coframe point))⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact
    (lorentzianMetric_inv_contDiffAt (current.coframe point)
      (nondegenerate point)).comp point
      (holonomicCoframe_contDiff current smooth).contDiffAt

private theorem temporalPrincipal_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    ContDiff ℝ ∞ (fun point =>
      coframeTemporalPrincipalScalar (current.coframe point)) := by
  rw [show (fun point =>
      coframeTemporalPrincipalScalar (current.coframe point)) =
      fun point =>
        -((lorentzianMetricOfCoframe (current.coframe point))⁻¹ 0 0) by
    funext point
    rw [lorentzianMetricOfCoframe_inv_time_time_eq_neg_temporalPrincipalScalar]
    ring]
  exact (contDiff_pi.mp
    (contDiff_pi.mp (inverseMetric_contDiff current smooth nondegenerate) 0) 0
    ).neg

private theorem normalCovariantVelocity_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiff ℝ ∞ (scalarNormalConstraintCovariantVelocity current) := by
  have metricRegular := inverseMetric_contDiff current smooth nondegenerate
  have scalarJetRegular (direction : LorentzianIndex) : ContDiff ℝ ∞
      (fun point => holonomicScalarCovariantDerivative current point
        direction) :=
    StageNineCoframeScalarMatterRegularity.holonomicScalarCovariantDerivative_contDiff_local
      current smooth direction
  have demandRegular : ContDiff ℝ ∞
      (scalarNormalConstraintSpatialDemand current) := by
    unfold scalarNormalConstraintSpatialDemand
    apply ContDiff.sum
    intro axis _
    exact
      (contDiff_pi.mp (contDiff_pi.mp metricRegular 0) axis.succ).smul
        (scalarJetRegular axis.succ)
  have inversePrincipalRegular : ContDiff ℝ ∞ (fun point =>
      (coframeTemporalPrincipalScalar (current.coframe point))⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro point
    exact (temporalPrincipal_contDiff current smooth nondegenerate).contDiffAt.inv
      (noncharacteristic point)
  exact inversePrincipalRegular.smul demandRegular

private theorem normalRawVelocity_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    ContDiff ℝ ∞ (fun point : BasePoint =>
      scalarNormalConstraintRawVelocity current
        (canonicalSpatialProjection point)) := by
  let slice := fun point : BasePoint =>
    canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)
  have normalRegular : ContDiff ℝ ∞ (fun point =>
      scalarNormalConstraintCovariantVelocity current (slice point)) :=
    (normalCovariantVelocity_contDiff current smooth nondegenerate
      noncharacteristic).comp zeroSliceProjection_contDiff
  have connectionRegular : ContDiff ℝ ∞ (fun point =>
      holonomicP286GaugeConnectionCoordinate current (slice point)
        canonicalLorentzianTimeDirection) :=
    (smooth.2.2.2.2.1 canonicalLorentzianTimeDirection).comp
      zeroSliceProjection_contDiff
  have scalarRegular : ContDiff ℝ ∞ (fun point =>
      current.scalar (slice point)) :=
    smooth.2.2.2.2.2.2.1.comp zeroSliceProjection_contDiff
  have actionRegular : ContDiff ℝ ∞ (fun point =>
      StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate current (slice point)
          canonicalLorentzianTimeDirection)
        (current.scalar (slice point))) :=
    (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.comp
      connectionRegular).clm_apply scalarRegular
  rw [show (fun point : BasePoint =>
      scalarNormalConstraintRawVelocity current
        (canonicalSpatialProjection point)) =
      fun point =>
        scalarNormalConstraintCovariantVelocity current (slice point) -
          StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
            (holonomicP286GaugeConnectionCoordinate current (slice point)
              canonicalLorentzianTimeDirection)
            (current.scalar (slice point)) by
    funext point
    change
      scalarNormalConstraintCovariantVelocity current (slice point) -
          scalarMotherLieAction
            (p286LieBlockEmbed
              (current.gaugeConnection (slice point)
                canonicalLorentzianTimeDirection))
            (current.scalar (slice point)) =
        scalarNormalConstraintCovariantVelocity current (slice point) -
          scalarMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (p286CoordinateEquiv
                  (current.gaugeConnection (slice point)
                    canonicalLorentzianTimeDirection))))
            (current.scalar (slice point))
    rw [p286CoordinateEquiv.symm_apply_apply]]
  exact normalRegular.sub actionRegular

/-- Smoothness is a downstream qualification of the total source/current
formula, not a constructor field. -/
theorem normalConstraint_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (noncharacteristic : ∀ point,
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth, ?_,
    matterSmooth, conjugateMatterSmooth⟩
  have anchorRegular : ContDiff ℝ ∞ (fun point : BasePoint =>
      current.scalar
        (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))) :=
    scalarSmooth.comp zeroSliceProjection_contDiff
  exact anchorRegular.add
    (canonicalTimeProjection.contDiff.smul
      (normalRawVelocity_contDiff current
        ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
          multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
          scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
        nondegenerate noncharacteristic))

/-- The written scalar has exactly the generated covariant time velocity. -/
theorem normalConstraint_scalarCovariantDerivative_time_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (generatedDifferentiable : DifferentiableAt ℝ
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
        current).scalar
      (canonicalCauchySlicePoint 0 space)) :
    holonomicScalarCovariantDerivative
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      scalarNormalConstraintCovariantVelocity current
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicScalarCovariantDerivative
  rw [normalConstraint_scalar_temporalDerivative_of_differentiable
    current space generatedDifferentiable,
    normalConstraint_scalar_zeroSlice]
  unfold scalarNormalConstraintRawVelocity
  change
    scalarNormalConstraintCovariantVelocity current
          (canonicalCauchySlicePoint 0 space) -
        scalarMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection (canonicalCauchySlicePoint 0 space)
              canonicalLorentzianTimeDirection))
          (current.scalar (canonicalCauchySlicePoint 0 space)) +
      scalarMotherLieAction
        (p286LieBlockEmbed
          (current.gaugeConnection (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection))
        (current.scalar (canonicalCauchySlicePoint 0 space)) = _
  abel

/-- Spatial covariant first jets are inherited on the same initial slice. -/
theorem normalConstraint_scalarCovariantDerivative_spatial_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) (axis : Fin 3)
    (currentDifferentiable : DifferentiableAt ℝ current.scalar
      (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable : DifferentiableAt ℝ
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
        current).scalar
      (canonicalCauchySlicePoint 0 space)) :
    holonomicScalarCovariantDerivative
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current)
        (canonicalCauchySlicePoint 0 space) axis.succ =
      holonomicScalarCovariantDerivative current
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  unfold holonomicScalarCovariantDerivative
  rw [normalConstraint_scalar_spatialDerivative_zeroSlice current space axis
    currentDifferentiable generatedDifferentiable,
    normalConstraint_scalar_zeroSlice]
  rfl

/-! ## Normal momentum settlement -/

private theorem inverseMetric_time_time_eq_neg_principal
    (current : StageNineHolonomicConfiguration) (point : BasePoint) :
    (lorentzianMetricOfCoframe (current.coframe point))⁻¹ 0 0 =
      -coframeTemporalPrincipalScalar (current.coframe point) :=
  lorentzianMetricOfCoframe_inv_time_time_eq_neg_temporalPrincipalScalar _

theorem normalConstraint_inverseMetric_timeRow_contraction_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (principalNonzero :
      coframeTemporalPrincipalScalar
        (current.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0)
    (currentDifferentiable : DifferentiableAt ℝ current.scalar
      (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable : DifferentiableAt ℝ
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
        current).scalar
      (canonicalCauchySlicePoint 0 space)) :
    ∑ direction : LorentzianIndex,
        (((lorentzianMetricOfCoframe
          ((p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
            current).coframe (canonicalCauchySlicePoint 0 space)))⁻¹)
            0 direction) •
          holonomicScalarCovariantDerivative
            (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
              current)
            (canonicalCauchySlicePoint 0 space) direction = 0 := by
  simp only [normalConstraint_coframe]
  rw [Fin.sum_univ_succ]
  have timeEq :=
    normalConstraint_scalarCovariantDerivative_time_zeroSlice current space
      generatedDifferentiable
  change
    holonomicScalarCovariantDerivative
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current) (canonicalCauchySlicePoint 0 space) 0 = _ at timeEq
  rw [timeEq]
  simp_rw [normalConstraint_scalarCovariantDerivative_spatial_zeroSlice
    current space _ currentDifferentiable generatedDifferentiable]
  rw [inverseMetric_time_time_eq_neg_principal]
  unfold scalarNormalConstraintCovariantVelocity
    scalarNormalConstraintSpatialDemand
  rw [smul_smul]
  have coefficient :
      -coframeTemporalPrincipalScalar
          (current.coframe (canonicalCauchySlicePoint 0 space)) *
          (coframeTemporalPrincipalScalar
            (current.coframe (canonicalCauchySlicePoint 0 space)))⁻¹ =
        -1 := by
    rw [neg_mul, mul_inv_cancel₀ principalNonzero]
  rw [coefficient, neg_one_smul]
  abel

private theorem scalarCoordinatePairingRe_comm_local
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second =
      scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re, mul_comm]

private theorem scalarCoordinatePairingRe_zero_left_local
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe 0 value = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_zero_right_local
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe value 0 = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem inverseLorentzianMetric_isSymm
    (coframe : LorentzianCoframe) :
    ((lorentzianMetricOfCoframe coframe)⁻¹).IsSymm := by
  apply Matrix.IsSymm.inv
  unfold Matrix.IsSymm lorentzianMetricOfCoframe
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  simp [minkowskiInternalMetric, Matrix.mul_assoc]

private theorem scalarTemporalMomentumDualAt_eq_timeRowPairing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : ScalarCoordinateCarrier) :
    scalarTemporalMomentumDualAt source current point direction =
      generatedVolumeDensity (toContinuumPointField current point) *
        scalarCoordinatePairingRe direction
          (∑ derivativeDirection : LorentzianIndex,
            (((lorentzianMetricOfCoframe (current.coframe point))⁻¹)
              0 derivativeDirection) •
              holonomicScalarCovariantDerivative current point
                derivativeDirection) := by
  unfold scalarTemporalMomentumDualAt scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    scalarVariationDifferentialDirection
  simp only [toContinuumPointField,
    StageNineP286GaugeConnectionVariationDensity.scalarFrameRelativeCoordinates_zeroChart]
  simp only [Fin.sum_univ_four]
  simp [canonicalLorentzianTimeDirection,
    scalarCoordinatePairingRe_zero_left_local,
    scalarCoordinatePairingRe_zero_right_local,
    scalarCoordinatePairingRe_add_right,
    scalarCoordinatePairingRe_real_smul_right]
  have metricSymm := inverseLorentzianMetric_isSymm (current.coframe point)
  rw [metricSymm.apply 0 1, metricSymm.apply 0 2,
    metricSymm.apply 0 3]
  rw [scalarCoordinatePairingRe_comm_local
      (holonomicScalarCovariantDerivative current point 0) direction,
    scalarCoordinatePairingRe_comm_local
      (holonomicScalarCovariantDerivative current point 1) direction,
    scalarCoordinatePairingRe_comm_local
      (holonomicScalarCovariantDerivative current point 2) direction,
    scalarCoordinatePairingRe_comm_local
      (holonomicScalarCovariantDerivative current point 3) direction]
  ring_nf
  simp

theorem normalConstraint_scalarTemporalMomentum_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (principalNonzero :
      coframeTemporalPrincipalScalar
        (current.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0)
    (currentDifferentiable : DifferentiableAt ℝ current.scalar
      (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable : DifferentiableAt ℝ
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
        current).scalar
      (canonicalCauchySlicePoint 0 space))
    (direction : ScalarCoordinateCarrier) :
    scalarTemporalMomentumDualAt source
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current)
        (canonicalCauchySlicePoint 0 space) direction = 0 := by
  rw [scalarTemporalMomentumDualAt_eq_timeRowPairing]
  rw [normalConstraint_inverseMetric_timeRow_contraction_zeroSlice current
    space principalNonzero currentDifferentiable generatedDifferentiable]
  simp [scalarCoordinatePairingRe]

/-- Direct P286 consumer: zero normal scalar momentum kills the scalar
contribution to every temporal gauge variation on the initial slice. -/
theorem normalConstraint_p286ScalarCurrent_temporal_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (principalNonzero :
      coframeTemporalPrincipalScalar
        (current.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0)
    (currentDifferentiable : DifferentiableAt ℝ current.scalar
      (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable : DifferentiableAt ℝ
      (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
        current).scalar
      (canonicalCauchySlicePoint 0 space))
    (component : P286CoordinateCarrier) :
    p286ScalarCurrentCoefficient source
        (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
          current)
        (p286TemporalGaugeOneForm component)
        (canonicalCauchySlicePoint 0 space) = 0 := by
  let generated :=
    p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
      current
  let scalarDirection :=
    StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
      component
      (generated.scalar (canonicalCauchySlicePoint 0 space))
  have momentumZero :=
    normalConstraint_scalarTemporalMomentum_zeroSlice source current space
      principalNonzero currentDifferentiable generatedDifferentiable
      scalarDirection
  change
    generatedVolumeDensity
        (toContinuumPointField generated
          (canonicalCauchySlicePoint 0 space)) *
      scalarGaugeConnectionKineticFirstVariationDensity source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField generated
          (canonicalCauchySlicePoint 0 space))
        (holonomicScalarGaugeConnectionVariation generated
          (fun _ => p286TemporalGaugeOneForm component)
          (canonicalCauchySlicePoint 0 space)) = 0
  have variationEq :
      holonomicScalarGaugeConnectionVariation generated
          (fun _ => p286TemporalGaugeOneForm component)
          (canonicalCauchySlicePoint 0 space) =
        scalarVariationDifferentialDirection scalarDirection
          canonicalLorentzianTimeDirection := by
    funext formDirection
    unfold holonomicScalarGaugeConnectionVariation
      p286GaugeConnectionMotherVariation scalarDirection generated
    fin_cases formDirection <;>
      simp [p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection,
        scalarVariationDifferentialDirection,
        StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear]
  rw [variationEq]
  exact momentumZero

end
end StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
end PhysicsCore
end SaturationMonoid
