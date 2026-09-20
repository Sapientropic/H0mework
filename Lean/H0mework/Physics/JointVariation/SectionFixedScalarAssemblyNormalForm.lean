import H0mework.Physics.JointVariation.SectionFixedMatterAssemblyNormalForm

/-!
# Fixed P506/L0 scalar assembly normal form

For the same source/current-only global section used by the complete-joint
producer, this module computes the scalar-covariant assembly seam.  The
matching contact and the global section carry the same action-generated
quadratic temporal acceleration at the same occurrence.  Their temporal
first jets therefore cancel; the only possible seam is the spatial
derivative of that source-owned acceleration profile, multiplied by the
canonical quadratic-time coefficient.

No seam coordinate is consumed by a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506ScalarAssemblyNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonPointwiseJointResidualNormalForm
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeFixedP506ScalarAccelerationSpatialRegularity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineScalarActionSecondJetLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev GlobalActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

/-- The scalar acceleration profile generated from the fixed P506/L0
source-owned contact family. -/
def fixedP506L0CompleteJointScalarSpatialAcceleration
    (space : StageNineSpatialPoint) : ScalarCoordinateCarrier :=
  recenteredContactDiracDualScalarAcceleration space

/-- The quadratic action contribution assembled into the global scalar
field. -/
def fixedP506L0CompleteJointScalarSectionCorrection
    (point : BasePoint) : ScalarCoordinateCarrier :=
  scalarQuadraticTimeCoefficient point •
    fixedP506L0CompleteJointScalarSpatialAcceleration
      (canonicalSpatialProjection point)

/-- The same quadratic contribution in the matching local contact. -/
def fixedP506L0CompleteJointScalarContactCorrection
    (point localPoint : BasePoint) : ScalarCoordinateCarrier :=
  scalarQuadraticTimeCoefficient localPoint •
    fixedP506L0CompleteJointScalarSpatialAcceleration
      (canonicalSpatialProjection point)

theorem fixedP506L0CompleteJointScalarSpatialAcceleration_contDiff :
    ContDiff ℝ ∞ fixedP506L0CompleteJointScalarSpatialAcceleration := by
  exact recenteredContactDiracDualScalarAcceleration_contDiff

theorem fixedP506L0CompleteJointScalarSectionCorrection_contDiff :
    ContDiff ℝ ∞ fixedP506L0CompleteJointScalarSectionCorrection := by
  unfold fixedP506L0CompleteJointScalarSectionCorrection
  have coefficientSmooth : ContDiff ℝ ∞ scalarQuadraticTimeCoefficient := by
    unfold scalarQuadraticTimeCoefficient
    fun_prop
  exact
    coefficientSmooth.smul
      (fixedP506L0CompleteJointScalarSpatialAcceleration_contDiff.comp
        canonicalSpatialProjection.contDiff)

theorem fixedP506L0CompleteJointScalarContactCorrection_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞
      (fixedP506L0CompleteJointScalarContactCorrection point) := by
  unfold fixedP506L0CompleteJointScalarContactCorrection
  have coefficientSmooth : ContDiff ℝ ∞ scalarQuadraticTimeCoefficient := by
    unfold scalarQuadraticTimeCoefficient
    fun_prop
  exact coefficientSmooth.smul contDiff_const

private theorem globalScalar_eq_input_add_correction :
    GlobalActual.scalar =
      fun point =>
        InputActual.scalar point +
          fixedP506L0CompleteJointScalarSectionCorrection point := by
  funext point
  rw [fixedP506L0CompleteJointActionSpacetimeSection_scalar_normalForm]
  simp [fixedP506L0CompleteJointScalarSectionCorrection,
    fixedP506L0CompleteJointScalarSpatialAcceleration,
    scalarQuadraticTimeCorrection, scalarQuadraticTimeCoefficient,
    canonicalTimeProjection]

private theorem matchingContactScalar_eq_inputComp_add_correction
    (point : BasePoint) :
    (fixedP506L0CompleteJointActionMatchingContact point).scalar =
      fun localPoint =>
        InputActual.scalar
            (canonicalSpatialContactTranslation
              (canonicalSpatialProjection point) localPoint) +
          fixedP506L0CompleteJointScalarContactCorrection point localPoint := by
  funext localPoint
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  rw [fixedP506L0FinalCommonActionActual_scalar_point_normalForm]
  simp [fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration,
    fixedP506L0CompleteJointScalarContactCorrection,
    fixedP506L0CompleteJointScalarSpatialAcceleration,
    scalarQuadraticTimeCorrection]

private theorem fieldDirectionalDerivative_add_scalarCoordinates
    (first second : BasePoint → ScalarCoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => first candidate + second candidate)
        point direction =
      fieldDirectionalDerivative first point direction +
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

private theorem inputScalar_comp_translation_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞
      (fun localPoint =>
        InputActual.scalar
          (canonicalSpatialContactTranslation space localPoint)) := by
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1.comp
      (by
        unfold canonicalSpatialContactTranslation
        fun_prop)

private theorem globalScalarDerivative_normalForm
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative GlobalActual.scalar point direction =
      fieldDirectionalDerivative InputActual.scalar point direction +
        fieldDirectionalDerivative
          fixedP506L0CompleteJointScalarSectionCorrection point direction := by
  rw [globalScalar_eq_input_add_correction]
  exact fieldDirectionalDerivative_add_scalarCoordinates
    InputActual.scalar fixedP506L0CompleteJointScalarSectionCorrection
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
    fixedP506L0CompleteJointScalarSectionCorrection_contDiff point direction

private theorem matchingContactScalarDerivative_normalForm
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fixedP506L0CompleteJointActionMatchingContact point).scalar
        (completeJointActionMatchingContactPoint point) direction =
      fieldDirectionalDerivative
          (fun localPoint =>
            InputActual.scalar
              (canonicalSpatialContactTranslation
                (canonicalSpatialProjection point) localPoint))
          (completeJointActionMatchingContactPoint point) direction +
        fieldDirectionalDerivative
          (fixedP506L0CompleteJointScalarContactCorrection point)
          (completeJointActionMatchingContactPoint point) direction := by
  rw [matchingContactScalar_eq_inputComp_add_correction]
  exact fieldDirectionalDerivative_add_scalarCoordinates
    (fun localPoint =>
      InputActual.scalar
        (canonicalSpatialContactTranslation
          (canonicalSpatialProjection point) localPoint))
    (fixedP506L0CompleteJointScalarContactCorrection point)
    (inputScalar_comp_translation_contDiff (canonicalSpatialProjection point))
    (fixedP506L0CompleteJointScalarContactCorrection_contDiff point)
    (completeJointActionMatchingContactPoint point) direction

private theorem inputScalarDerivative_eq_matchingTranslation
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun localPoint =>
          InputActual.scalar
            (canonicalSpatialContactTranslation
              (canonicalSpatialProjection point) localPoint))
        (completeJointActionMatchingContactPoint point) direction =
      fieldDirectionalDerivative InputActual.scalar point direction := by
  have translation :
      HasFDerivAt
        (canonicalSpatialContactTranslation (canonicalSpatialProjection point))
        (ContinuousLinearMap.id ℝ BasePoint)
        (completeJointActionMatchingContactPoint point) := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  have fieldDifferentiable :
      DifferentiableAt ℝ InputActual.scalar point :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      |>.differentiable (by simp)).differentiableAt
  have translatedPoint :
      canonicalSpatialContactTranslation
          (canonicalSpatialProjection point)
          (completeJointActionMatchingContactPoint point) =
        point := by
    rw [completeJointActionMatchingContactPoint,
      canonicalSpatialContactTranslation_timeAxis,
      canonicalCauchySlicePoint_projections]
  have composed :
      HasFDerivAt
        (InputActual.scalar ∘
          canonicalSpatialContactTranslation (canonicalSpatialProjection point))
        (fderiv ℝ InputActual.scalar point)
        (completeJointActionMatchingContactPoint point) := by
    have atTranslated :
        HasFDerivAt InputActual.scalar (fderiv ℝ InputActual.scalar point)
          (canonicalSpatialContactTranslation
            (canonicalSpatialProjection point)
            (completeJointActionMatchingContactPoint point)) := by
      simpa only [translatedPoint] using fieldDifferentiable.hasFDerivAt
    simpa using atTranslated.comp
      (completeJointActionMatchingContactPoint point) translation
  unfold fieldDirectionalDerivative
  have applied :=
    congrArg
      (fun derivative : BasePoint →L[ℝ] ScalarCoordinateCarrier =>
        derivative (coordinateDirection direction))
      composed.fderiv
  simpa only [Function.comp_def] using applied

private theorem scalarSectionCorrection_directionalDerivative
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        fixedP506L0CompleteJointScalarSectionCorrection point direction =
      fieldDirectionalDerivative scalarQuadraticTimeCoefficient point direction •
          fixedP506L0CompleteJointScalarSpatialAcceleration
            (canonicalSpatialProjection point) +
        scalarQuadraticTimeCoefficient point •
          fderiv ℝ fixedP506L0CompleteJointScalarSpatialAcceleration
              (canonicalSpatialProjection point)
            (canonicalSpatialProjection (coordinateDirection direction)) := by
  have accelerationDerivative :
      HasFDerivAt
        fixedP506L0CompleteJointScalarSpatialAcceleration
        (fderiv ℝ fixedP506L0CompleteJointScalarSpatialAcceleration
          (canonicalSpatialProjection point))
        (canonicalSpatialProjection point) :=
    (fixedP506L0CompleteJointScalarSpatialAcceleration_contDiff
      |>.differentiable (by simp) |>.differentiableAt).hasFDerivAt
  have composedAccelerationDerivative :
      HasFDerivAt
        (fixedP506L0CompleteJointScalarSpatialAcceleration ∘
          canonicalSpatialProjection)
        ((fderiv ℝ fixedP506L0CompleteJointScalarSpatialAcceleration
          (canonicalSpatialProjection point)).comp canonicalSpatialProjection)
        point :=
    accelerationDerivative.comp point canonicalSpatialProjection.hasFDerivAt
  have coefficientDerivative :
      HasFDerivAt scalarQuadraticTimeCoefficient
        (fderiv ℝ scalarQuadraticTimeCoefficient point) point :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt point
      ).differentiableAt.hasFDerivAt
  have correctionDerivative :=
    coefficientDerivative.smul composedAccelerationDerivative
  have functionEquality :
      fixedP506L0CompleteJointScalarSectionCorrection =
        scalarQuadraticTimeCoefficient •
          (fixedP506L0CompleteJointScalarSpatialAcceleration ∘
            canonicalSpatialProjection) := by
    rfl
  unfold fieldDirectionalDerivative
  rw [functionEquality, correctionDerivative.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, Function.comp_apply]
  abel

private theorem scalarContactCorrection_directionalDerivative
    (point localPoint : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fixedP506L0CompleteJointScalarContactCorrection point)
        localPoint direction =
      fieldDirectionalDerivative scalarQuadraticTimeCoefficient
          localPoint direction •
        fixedP506L0CompleteJointScalarSpatialAcceleration
          (canonicalSpatialProjection point) := by
  have derivative :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt localPoint).smul_const
      (fixedP506L0CompleteJointScalarSpatialAcceleration
        (canonicalSpatialProjection point))
  unfold fieldDirectionalDerivative
    fixedP506L0CompleteJointScalarContactCorrection
  rw [derivative.fderiv]
  rw [(scalarQuadraticTimeCoefficient_hasFDerivAt localPoint).fderiv]
  rfl

private theorem scalarQuadraticTimeCoefficient_directionalDerivative
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative scalarQuadraticTimeCoefficient point direction =
      if direction = canonicalLorentzianTimeDirection then
        canonicalTimeProjection point
      else
        0 := by
  unfold fieldDirectionalDerivative
  rw [(scalarQuadraticTimeCoefficient_hasFDerivAt point).fderiv]
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection,
      canonicalTimeProjection]
  ring

/-- Exact fixed-lineage scalar assembly normal form before simplifying the
two generated quadratic response derivatives. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_scalarCovariantDerivative_normalForm
    (point : BasePoint)
    (direction : LorentzianIndex) :
    (fixedP506L0CompleteJointActionSpacetimeAssemblySeam point
      ).scalarCovariantDerivative direction =
      fieldDirectionalDerivative
          fixedP506L0CompleteJointScalarSectionCorrection point direction -
        fieldDirectionalDerivative
          (fixedP506L0CompleteJointScalarContactCorrection point)
          (completeJointActionMatchingContactPoint point) direction := by
  have gaugeAt :
      GlobalActual.gaugeConnection point =
        (fixedP506L0CompleteJointActionMatchingContact point
          ).gaugeConnection
          (completeJointActionMatchingContactPoint point) :=
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection_at
      positiveSmoothUnifiedSource InputActual point
  have scalarAt :
      GlobalActual.scalar point =
        (fixedP506L0CompleteJointActionMatchingContact point).scalar
          (completeJointActionMatchingContactPoint point) :=
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_scalar_at
      positiveSmoothUnifiedSource InputActual point
  unfold fixedP506L0CompleteJointActionSpacetimeAssemblySeam
    completeJointActionJetAssemblySeam
    generatedDiracDualFormNativePointwiseActionJet
    toContinuumPointField
  simp only [Pi.sub_apply]
  unfold holonomicScalarCovariantDerivative
  rw [gaugeAt, scalarAt, globalScalarDerivative_normalForm,
    matchingContactScalarDerivative_normalForm,
    inputScalarDerivative_eq_matchingTranslation]
  abel

/-- The scalar-covariant assembly seam is exactly the spatial derivative of
the source/action-generated acceleration profile, weighted by the canonical
quadratic-time coefficient. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_scalarCovariantDerivative_spatialProfile
    (point : BasePoint)
    (direction : LorentzianIndex) :
    (fixedP506L0CompleteJointActionSpacetimeAssemblySeam point
      ).scalarCovariantDerivative direction =
      scalarQuadraticTimeCoefficient point •
        fderiv ℝ fixedP506L0CompleteJointScalarSpatialAcceleration
            (canonicalSpatialProjection point)
          (canonicalSpatialProjection (coordinateDirection direction)) := by
  rw [
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_scalarCovariantDerivative_normalForm,
    scalarSectionCorrection_directionalDerivative,
    scalarContactCorrection_directionalDerivative]
  rw [completeJointActionMatchingContactPoint]
  have coefficientDerivative :
      fieldDirectionalDerivative scalarQuadraticTimeCoefficient
          (canonicalCauchySlicePoint
            (canonicalTimeProjection point) 0) direction =
        fieldDirectionalDerivative scalarQuadraticTimeCoefficient
          point direction := by
    rw [scalarQuadraticTimeCoefficient_directionalDerivative,
      scalarQuadraticTimeCoefficient_directionalDerivative]
    simp
  rw [coefficientDerivative]
  abel

/-- The scalar-covariant assembly seam vanishes on the entire canonical
Cauchy slice. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_scalarCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    (fixedP506L0CompleteJointActionSpacetimeAssemblySeam
      (canonicalCauchySlicePoint 0 space)).scalarCovariantDerivative
        direction = 0 := by
  rw [
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_scalarCovariantDerivative_spatialProfile]
  simp [scalarQuadraticTimeCoefficient]

/-- On the complete zero slice, the explicit quadratic-time section carries
the scalar covariant first jet of the fixed input unchanged.  This is the
direct field-level consequence of the generated normal form; it is stronger
than merely observing that the section/contact assembly seam vanishes. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSection_scalarCovariantDerivative_zeroSlice_eq_input
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative GlobalActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative InputActual
        (canonicalCauchySlicePoint 0 space) := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [show GlobalActual.gaugeConnection = InputActual.gaugeConnection by
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource InputActual]
  rw [globalScalarDerivative_normalForm,
    scalarSectionCorrection_directionalDerivative]
  have scalarValue :
      GlobalActual.scalar (canonicalCauchySlicePoint 0 space) =
        InputActual.scalar (canonicalCauchySlicePoint 0 space) := by
    rw [fixedP506L0CompleteJointActionSpacetimeSection_scalar_normalForm]
    simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
    simp [scalarQuadraticTimeCorrection, scalarQuadraticTimeCoefficient,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection]
  rw [scalarValue]
  simp [scalarQuadraticTimeCoefficient,
    scalarQuadraticTimeCoefficient_directionalDerivative]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506ScalarAssemblyNormalForm
