import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.GaugeAction.P286ConnectionGeneratedScalarParallelTransport

/-!
# P286-connection-relative scalar Cauchy development

The scalar field is second order, so its zero-slice value does not determine
its temporal first jet.  This module realizes the horizontal first jet of the
canonical P286 representation orbit:

`D₀ φ = ∂₀ φ + A₀ · φ = 0`.

The operator reads only one primitive current.  It keeps the complete
zero-slice scalar value, reads the orbit tangent, and extends those Cauchy data
by the fixed affine time section.  It does not consume a residual, support
coordinate, target state, branch, or equation receipt.

This generic layer is a representation transporter and a read-after-write
diagnostic.  It does not prove that a scalar mother-action producer selected
the horizontal first jet.  Any downstream promotion to an authoritative
physical successor must separately discharge that producer-authority gate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP286ConnectionRelativeScalarCauchyDevelopmentOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeScalarMatterRegularity
open StageNineConnectionSectorSourceBalance
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ConnectionGeneratedScalarParallelTransport
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance p286ConnectionRelativeScalarModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286ConnectionRelativeScalarCoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286ConnectionRelativeScalarCoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Native zero-slice relation -/

/-- The scalar value inherited at the canonical zero slice. -/
def p286ConnectionRelativeScalarZeroSliceAnchor
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) : ScalarCoordinateCarrier :=
  current.scalar (canonicalCauchySlicePoint 0 space)

/-- The temporal scalar velocity read from the canonical P286 representation
exponential generated at the same zero-slice occurrence. -/
def p286ConnectionRelativeScalarVelocity
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) : ScalarCoordinateCarrier :=
  p286ConnectionGeneratedScalarParallelVelocity current space

/-- Representation-provenance seam: the velocity installed by the affine
Cauchy first-jet realization is the derivative of the independently generated
P286 scalar parallel orbit.  This theorem is not scalar-action authority. -/
theorem p286ConnectionRelativeScalarVelocity_is_parallelOrbitDerivative
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    NormedHasDerivAt
      (p286ConnectionGeneratedScalarParallelOrbit current space)
      (p286ConnectionRelativeScalarVelocity current space) 0 := by
  exact p286ConnectionGeneratedScalarParallelOrbit_hasDerivAt_zero
    current space

/-- Canonical affine spacetime section of the connection-relative scalar
Cauchy data.  All eight other primitive fields are inherited verbatim. -/
def p286ConnectionRelativeScalarCauchyDevelopmentOperator
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    scalar := fun point =>
      p286ConnectionRelativeScalarZeroSliceAnchor current
          (canonicalSpatialProjection point) +
        canonicalTimeProjection point •
          p286ConnectionRelativeScalarVelocity current
            (canonicalSpatialProjection point) }

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_coframe
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_gravityConnection
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
      ).gravityConnection = current.gravityConnection :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_gravityAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
      ).gravityAuxiliary = current.gravityAuxiliary :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_gravitySimplicityMultiplier
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
      ).gravitySimplicityMultiplier = current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_gaugeConnection
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
      ).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_gaugeAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
      ).gaugeAuxiliary = current.gaugeAuxiliary :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_matter
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).matter =
      current.matter :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_conjugateMatter
    (current : StageNineHolonomicConfiguration) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
      ).conjugateMatter = current.conjugateMatter :=
  rfl

@[simp] theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
        (canonicalCauchySlicePoint 0 space) =
      current.scalar (canonicalCauchySlicePoint 0 space) := by
  simp [p286ConnectionRelativeScalarCauchyDevelopmentOperator,
    p286ConnectionRelativeScalarZeroSliceAnchor]

/-! ## Regularity and faithful temporal first jet -/

theorem p286ConnectionRelativeScalarCauchyDevelopmentOperator_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth, ?_,
    matterSmooth, conjugateMatterSmooth⟩
  have zeroSliceSmooth : ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext space
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
      simp]
    exact canonicalSpatialInclusion.contDiff
  have sliceSmooth : ContDiff ℝ ∞ (fun point : BasePoint =>
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) := by
    exact zeroSliceSmooth.comp canonicalSpatialProjection.contDiff
  have anchorSmooth : ContDiff ℝ ∞ (fun point : BasePoint =>
      p286ConnectionRelativeScalarZeroSliceAnchor current
        (canonicalSpatialProjection point)) := by
    exact scalarSmooth.comp sliceSmooth
  have connectionSmooth : ContDiff ℝ ∞ (fun point : BasePoint =>
      p286CoordinateEquiv
        (current.gaugeConnection
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))
          canonicalLorentzianTimeDirection)) := by
    exact (gaugeConnectionSmooth canonicalLorentzianTimeDirection).comp
      sliceSmooth
  have velocitySmooth : ContDiff ℝ ∞ (fun point : BasePoint =>
      p286ConnectionRelativeScalarVelocity current
        (canonicalSpatialProjection point)) := by
    unfold p286ConnectionRelativeScalarVelocity
    exact ((scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.comp
      connectionSmooth).clm_apply anchorSmooth).neg
  unfold p286ConnectionRelativeScalarCauchyDevelopmentOperator
  exact anchorSmooth.add
    ((by fun_prop : ContDiff ℝ ∞ canonicalTimeProjection).smul
      velocitySmooth)

/-- Along each canonical time line the generated scalar has exactly the
connection-relative velocity selected on that spatial occurrence. -/
theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_timeLine_hasDerivAt
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    NormedHasDerivAt
      (fun candidateTime =>
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
          ).scalar (canonicalCauchySlicePoint candidateTime space))
      (p286ConnectionRelativeScalarVelocity current space) time := by
  have generated :
      NormedHasDerivAt
        (fun candidateTime =>
          p286ConnectionRelativeScalarZeroSliceAnchor current space +
            candidateTime •
              p286ConnectionRelativeScalarVelocity current space)
        (p286ConnectionRelativeScalarVelocity current space) time := by
    unfold NormedHasDerivAt
    rw [hasDerivAt_const_add_iff]
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id time).smul_const
        (p286ConnectionRelativeScalarVelocity current space)
  have fieldEq :
      (fun candidateTime =>
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current
          ).scalar (canonicalCauchySlicePoint candidateTime space)) =
        fun candidateTime =>
          p286ConnectionRelativeScalarZeroSliceAnchor current space +
            candidateTime •
              p286ConnectionRelativeScalarVelocity current space := by
    funext candidateTime
    simp [p286ConnectionRelativeScalarCauchyDevelopmentOperator]
  rw [fieldEq]
  exact generated

/-- The ambient temporal derivative of a differentiable generated section is
the same native velocity, not merely a derivative of a detached time curve. -/
theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_temporalDerivative_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      p286ConnectionRelativeScalarVelocity current space := by
  have ambientLine :=
    field_timeLine_hasDerivAt
      (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
      space 0 generatedDifferentiable
  have nativeLine :=
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_timeLine_hasDerivAt
      current space 0
  simpa using ambientLine.unique nativeLine

/-- Smooth-current convenience form of the faithful temporal derivative. -/
theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_temporalDerivative
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      p286ConnectionRelativeScalarVelocity current space :=
  p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_temporalDerivative_of_differentiable
    current space
    ((p286ConnectionRelativeScalarCauchyDevelopmentOperator_smooth
      current smooth).2.2.2.2.2.2.1.differentiable (by simp)
      |>.differentiableAt)

private theorem fderiv_canonicalCauchySlicePoint_spatial_local
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint time) space
        (canonicalSpatialCoordinateDirection direction) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space) direction.succ := by
  have derivative :=
    differentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-- Every spatial first jet on the generated zero slice is inherited from
the supplied current.  Together with the native temporal derivative above,
this is the complete Cauchy first-jet contract of the operator. -/
theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (currentDifferentiable :
      DifferentiableAt ℝ current.scalar
        (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
        (canonicalCauchySlicePoint 0 space) direction.succ =
      fieldDirectionalDerivative current.scalar
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  rw [← fderiv_canonicalCauchySlicePoint_spatial_local
      (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
      0 space direction generatedDifferentiable,
    ← fderiv_canonicalCauchySlicePoint_spatial_local current.scalar
      0 space direction currentDifferentiable]
  have sliceEquality :
      (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar ∘
          canonicalCauchySlicePoint 0 =
        current.scalar ∘ canonicalCauchySlicePoint 0 := by
    funext candidateSpace
    exact
      p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_zeroSlice
        current candidateSpace
  rw [sliceEquality]

/-- Differentiability-local producer soundness for the generated zero slice. -/
theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_temporalCovariantDerivative_zeroSlice_of_differentiable
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    holonomicScalarCovariantDerivative
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection = 0 := by
  unfold holonomicScalarCovariantDerivative
  rw [
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_temporalDerivative_of_differentiable
      current space generatedDifferentiable,
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_scalar_zeroSlice]
  unfold p286ConnectionRelativeScalarVelocity
  rw [p286ConnectionGeneratedScalarParallelVelocity_eq_lieAction]
  unfold p286CurrentTemporalConnectionCoordinate
    p286CurrentScalarZeroSliceAnchor
  change
    -(scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (current.gaugeConnection (canonicalCauchySlicePoint 0 space)
                canonicalLorentzianTimeDirection))))
        (current.scalar (canonicalCauchySlicePoint 0 space))) +
      scalarMotherLieAction
        (p286LieBlockEmbed
          (current.gaugeConnection (canonicalCauchySlicePoint 0 space)
            canonicalLorentzianTimeDirection))
        (current.scalar (canonicalCauchySlicePoint 0 space)) = 0
  rw [p286CoordinateEquiv.symm_apply_apply]
  abel

/-- Producer soundness: on the generated zero slice the temporal scalar
covariant derivative vanishes identically. -/
theorem
    p286ConnectionRelativeScalarCauchyDevelopmentOperator_temporalCovariantDerivative_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        (p286ConnectionRelativeScalarCauchyDevelopmentOperator current)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection = 0 :=
  p286ConnectionRelativeScalarCauchyDevelopmentOperator_temporalCovariantDerivative_zeroSlice_of_differentiable
    current space
    ((p286ConnectionRelativeScalarCauchyDevelopmentOperator_smooth
      current smooth).2.2.2.2.2.2.1.differentiable (by simp)
      |>.differentiableAt)

/-! ## Temporal P286-current settlement -/

/-- On an identity-coframe occurrence, a temporal P286 variation can only
pair with the temporal scalar covariant derivative.  Hence the horizontal
relation generated above removes the scalar contribution to that action
channel without reading a residual coordinate. -/
theorem p286ScalarCurrentCoefficient_temporal_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (component : P286CoordinateCarrier)
    (coframeEq : configuration.coframe point = 1)
    (temporalCovariantDerivativeZero :
      holonomicScalarCovariantDerivative configuration point
          canonicalLorentzianTimeDirection = 0) :
    p286ScalarCurrentCoefficient source configuration
        (p286TemporalGaugeOneForm component) point = 0 := by
  change (holonomicScalarCovariantDerivative configuration point 0 = 0) at temporalCovariantDerivativeZero
  unfold p286ScalarCurrentCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [coframeEq]
  simp only [Matrix.det_one, abs_one, one_mul]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [
    StageNineP286GaugeConnectionVariationDensity.scalarFrameRelativeCoordinates_zeroChart]
  rw [
    StageNinePositiveSourceNativeGravityCurvatureBridge.lorentzianMetricOfCoframe_one_inv]
  simp only [Fin.sum_univ_four]
  rw [temporalCovariantDerivativeZero]
  simp [minkowskiInternalMetric, p286TemporalGaugeOneForm,
    canonicalLorentzianTimeDirection,
    scalarCoordinatePairingRe]

/-- A vanishing complete scalar covariant first jet kills the scalar current
for every P286 one-form variation.  This is independent of a frame convention
because the zero jet is annihilated before the frame contraction. -/
theorem p286ScalarCurrentCoefficient_eq_zero_of_covariantDerivative_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : P286GaugeOneForm)
    (covariantDerivativeZero :
      holonomicScalarCovariantDerivative configuration point = 0) :
    p286ScalarCurrentCoefficient source configuration direction point = 0 := by
  unfold p286ScalarCurrentCoefficient generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField,
    StageNineP286GaugeConnectionVariationDensity.scalarFrameRelativeCoordinates_zeroChart]
  rw [covariantDerivativeZero]
  simp [scalarCoordinatePairingRe]

end

end
  SaturationMonoid.PhysicsCore.StageNineP286ConnectionRelativeScalarCauchyDevelopmentOperator
