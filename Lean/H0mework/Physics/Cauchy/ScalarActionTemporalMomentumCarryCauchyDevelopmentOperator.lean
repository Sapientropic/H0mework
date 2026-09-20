import H0mework.Physics.Exterior.ScalarActionTemporalMomentumLegendreVelocity
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator

/-!
# Scalar-action temporal-momentum carry Cauchy development

A downstream connection write changes the decomposition

`D₀ φ = ∂₀ φ + A₀ · φ`

even when the scalar canonical momentum should be carried unchanged.  This
module constructs the corresponding raw temporal scalar first jet in the
forward direction:

```text
reference source/action momentum
-> unique covariant velocity
+ current connection and scalar anchor
-> unique raw temporal first jet
-> affine Cauchy development.
```

The operator accepts only a source, a momentum-reference current, and the
current on which the scalar is installed.  It does not inspect an Euler
residual, a support coordinate, a demanded target, or a branch witness.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineScalarActionTemporalMomentumLegendreVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

/-- Raw scalar temporal velocity which carries the reference action momentum
through the current connection. -/
def scalarActionTemporalMomentumCarryVelocity
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) : ScalarCoordinateCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  scalarTemporalCovariantVelocityOfMomentum source reference point -
    scalarMotherLieAction
      (p286LieBlockEmbed
        (current.gaugeConnection point canonicalLorentzianTimeDirection))
      (current.scalar point)

/-- Affine spacetime realization of the carried scalar Cauchy data.  The
other eight primitive fields are inherited from `current`. -/
def scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    scalar := fun point =>
      current.scalar
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) +
        canonicalTimeProjection point •
          scalarActionTemporalMomentumCarryVelocity source reference current
            (canonicalSpatialProjection point) }

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_coframe
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).coframe = current.coframe :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gravityConnection
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).gravityConnection =
        current.gravityConnection :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).gravityAuxiliary = current.gravityAuxiliary :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gravitySimplicityMultiplier
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).gravitySimplicityMultiplier =
        current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).gaugeAuxiliary = current.gaugeAuxiliary :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_matter
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).matter = current.matter :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).conjugateMatter = current.conjugateMatter :=
  rfl

@[simp] theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_zeroSlice
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
      source reference current).scalar
        (canonicalCauchySlicePoint 0 space) =
      current.scalar (canonicalCauchySlicePoint 0 space) := by
  simp [scalarActionTemporalMomentumCarryCauchyDevelopmentOperator]

/-- The generated time line has exactly the action/connection-derived raw
velocity. -/
theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_timeLine_hasDerivAt
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    NormedHasDerivAt
      (fun candidateTime =>
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
          (canonicalCauchySlicePoint candidateTime space))
      (scalarActionTemporalMomentumCarryVelocity source reference current
        space)
      time := by
  have generated :
      NormedHasDerivAt
        (fun candidateTime =>
          current.scalar (canonicalCauchySlicePoint 0 space) +
            candidateTime •
              scalarActionTemporalMomentumCarryVelocity source reference
                current space)
        (scalarActionTemporalMomentumCarryVelocity source reference current
          space)
        time := by
    unfold NormedHasDerivAt
    rw [hasDerivAt_const_add_iff]
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id time).smul_const
        (scalarActionTemporalMomentumCarryVelocity source reference current
          space)
  have fieldEq :
      (fun candidateTime =>
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
          (canonicalCauchySlicePoint candidateTime space)) =
        fun candidateTime =>
          current.scalar (canonicalCauchySlicePoint 0 space) +
            candidateTime •
              scalarActionTemporalMomentumCarryVelocity source reference
                current space := by
    funext candidateTime
    simp [scalarActionTemporalMomentumCarryCauchyDevelopmentOperator]
  rw [fieldEq]
  exact generated

/-- Ambient temporal derivative of a differentiable carried section. -/
theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_temporalDerivative_of_differentiable
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      scalarActionTemporalMomentumCarryVelocity source reference current
        space := by
  have ambientLine :=
    field_timeLine_hasDerivAt
      (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
        source reference current).scalar
      space 0 generatedDifferentiable
  have nativeLine :=
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_timeLine_hasDerivAt
      source reference current space 0
  simpa using ambientLine.unique nativeLine

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

/-- The generated zero slice inherits all three raw spatial scalar
derivatives from `current`. -/
theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (currentDifferentiable :
      DifferentiableAt ℝ current.scalar
        (canonicalCauchySlicePoint 0 space))
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    fieldDirectionalDerivative
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
        (canonicalCauchySlicePoint 0 space) direction.succ =
      fieldDirectionalDerivative current.scalar
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  rw [← fderiv_canonicalCauchySlicePoint_spatial_local
      (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
        source reference current).scalar
      0 space direction generatedDifferentiable,
    ← fderiv_canonicalCauchySlicePoint_spatial_local current.scalar
      0 space direction currentDifferentiable]
  have sliceEquality :
      (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar ∘ canonicalCauchySlicePoint 0 =
        current.scalar ∘ canonicalCauchySlicePoint 0 := by
    funext candidateSpace
    exact
      scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_zeroSlice
        source reference current candidateSpace
  rw [sliceEquality]

/-- The raw first jet installs exactly the covariant velocity selected by the
reference scalar action. -/
theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_temporalCovariantDerivative_zeroSlice
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
        (canonicalCauchySlicePoint 0 space)) :
    holonomicScalarCovariantDerivative
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current)
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      scalarTemporalCovariantVelocityOfMomentum source reference
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicScalarCovariantDerivative
  rw [
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_temporalDerivative_of_differentiable
      source reference current space generatedDifferentiable,
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_zeroSlice]
  unfold scalarActionTemporalMomentumCarryVelocity
  simp only [
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gaugeConnection]
  abel

/-- Producer soundness: at identity-coframe reference and target occurrences,
the generated current carries exactly the same temporal scalar momentum. -/
theorem
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_momentum_preserved_zeroSlice
    (source : SmoothUnifiedSource)
    (reference current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (referenceCoframe :
      reference.coframe (canonicalCauchySlicePoint 0 space) = 1)
    (currentCoframe :
      current.coframe (canonicalCauchySlicePoint 0 space) = 1)
    (generatedDifferentiable :
      DifferentiableAt ℝ
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current).scalar
        (canonicalCauchySlicePoint 0 space))
    (direction : ScalarCoordinateCarrier) :
    scalarTemporalMomentumDualAt source
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
          source reference current)
        (canonicalCauchySlicePoint 0 space) direction =
      scalarTemporalMomentumDualAt source reference
        (canonicalCauchySlicePoint 0 space) direction := by
  rw [scalarTemporalMomentumDualAt_apply_identityCoframe source
      (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
        source reference current)
      (canonicalCauchySlicePoint 0 space) (by simpa using currentCoframe),
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_temporalCovariantDerivative_zeroSlice
      source reference current space generatedDifferentiable,
    scalarTemporalCovariantVelocityOfMomentum_eq source reference
      (canonicalCauchySlicePoint 0 space) referenceCoframe,
    scalarTemporalMomentumDualAt_apply_identityCoframe source reference
      (canonicalCauchySlicePoint 0 space) referenceCoframe]

end

end
  SaturationMonoid.PhysicsCore.StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
