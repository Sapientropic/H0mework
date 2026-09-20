import H0mework.Physics.JointVariation.SectionFixedGlobalRegularity

/-!
# Fixed P506/L0 matter assembly normal form

The source/current-only complete-joint spacetime section is already one
global actual.  This module compares its primal-matter first jet with the
matching source/action contact without assuming that the assembly seam
vanishes.

The comparison is fixed-lineage and output-facing: after the primitive field
values and both connection values cancel, the complete matter-covariant seam
is exactly the derivative mismatch between

* the globally assembled, spatially varying action-response profile, and
* the same matching contact's fixed local response.

Neither profile mismatch nor its support is accepted by a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506MatterAssemblyNormalForm

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonPointwiseJointResidualNormalForm
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
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

/-- Faithful coordinates of the action-generated matter response at the
source-owned spatial contact. -/
def fixedP506L0CompleteJointMatterSpatialResponseCoordinates
    (space : StageNineSpatialPoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
    (diracDualCurrentCoframeMatterTimeResponseWrite
      (fixedP506L0CartanRestartActual space))

/-- The response contribution actually assembled into the one global
spacetime section. -/
def fixedP506L0CompleteJointMatterSectionCorrection
    (point : BasePoint) : MatterCoordinateCarrier :=
  canonicalTimeProjection point •
    fixedP506L0CompleteJointMatterSpatialResponseCoordinates
      (canonicalSpatialProjection point)

/-- The response contribution carried by the matching local contact. -/
def fixedP506L0CompleteJointMatterContactCorrection
    (point localPoint : BasePoint) : MatterCoordinateCarrier :=
  localPoint canonicalLorentzianTimeDirection •
    fixedP506L0CompleteJointMatterSpatialResponseCoordinates
      (canonicalSpatialProjection point)

theorem fixedP506L0CompleteJointMatterSpatialResponseCoordinates_contDiff :
    ContDiff ℝ ∞
      fixedP506L0CompleteJointMatterSpatialResponseCoordinates := by
  exact fixedP506L0CompleteJointMatterResponseWrite_contDiff

theorem fixedP506L0CompleteJointMatterSectionCorrection_contDiff :
    ContDiff ℝ ∞ fixedP506L0CompleteJointMatterSectionCorrection := by
  unfold fixedP506L0CompleteJointMatterSectionCorrection
  exact canonicalTimeProjection.contDiff.smul
    (fixedP506L0CompleteJointMatterSpatialResponseCoordinates_contDiff.comp
      canonicalSpatialProjection.contDiff)

theorem fixedP506L0CompleteJointMatterContactCorrection_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞
      (fixedP506L0CompleteJointMatterContactCorrection point) := by
  unfold fixedP506L0CompleteJointMatterContactCorrection
  fun_prop

private theorem globalMatterCoordinates_eq_input_add_correction :
    (fun point => matterCoordinateEquiv (GlobalActual.matter point)) =
      fun point =>
        matterCoordinateEquiv (InputActual.matter point) +
          fixedP506L0CompleteJointMatterSectionCorrection point := by
  funext point
  rw [
    fixedP506L0CompleteJointActionSpacetimeSection_matter_normalForm]
  rfl

private theorem matchingContactMatterCoordinates_eq_inputComp_add_correction
    (point : BasePoint) :
    (fun localPoint =>
      matterCoordinateEquiv
        ((fixedP506L0CompleteJointActionMatchingContact point).matter
          localPoint)) =
      fun localPoint =>
        matterCoordinateEquiv
          (InputActual.matter
            (canonicalSpatialContactTranslation
              (canonicalSpatialProjection point) localPoint)) +
          fixedP506L0CompleteJointMatterContactCorrection point localPoint := by
  funext localPoint
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  rw [fixedP506L0FinalCommonActionActual_matter_point_normalForm]
  simp [fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration,
    matterLinearTimeCoordinateWrite,
    fixedP506L0CompleteJointMatterContactCorrection,
    fixedP506L0CompleteJointMatterSpatialResponseCoordinates]

private theorem fieldDirectionalDerivative_add_matterCoordinates
    (first second : BasePoint → MatterCoordinateCarrier)
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

private theorem inputMatterCoordinates_comp_translation_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞
      (fun localPoint =>
        matterCoordinateEquiv
          (InputActual.matter
            (canonicalSpatialContactTranslation space localPoint))) := by
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1.comp
      (by
        unfold canonicalSpatialContactTranslation
        fun_prop)

private theorem globalMatterCoordinateDerivative_normalForm
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (GlobalActual.matter candidate))
        point direction =
      fieldDirectionalDerivative
          (fun candidate =>
            matterCoordinateEquiv (InputActual.matter candidate))
          point direction +
        fieldDirectionalDerivative
          fixedP506L0CompleteJointMatterSectionCorrection point direction := by
  rw [globalMatterCoordinates_eq_input_add_correction]
  exact fieldDirectionalDerivative_add_matterCoordinates
    (fun candidate => matterCoordinateEquiv (InputActual.matter candidate))
    fixedP506L0CompleteJointMatterSectionCorrection
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
    fixedP506L0CompleteJointMatterSectionCorrection_contDiff point direction

private theorem matchingContactMatterCoordinateDerivative_normalForm
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun localPoint =>
          matterCoordinateEquiv
            ((fixedP506L0CompleteJointActionMatchingContact point).matter
              localPoint))
        (completeJointActionMatchingContactPoint point) direction =
      fieldDirectionalDerivative
          (fun localPoint =>
            matterCoordinateEquiv
              (InputActual.matter
                (canonicalSpatialContactTranslation
                  (canonicalSpatialProjection point) localPoint)))
          (completeJointActionMatchingContactPoint point) direction +
        fieldDirectionalDerivative
          (fixedP506L0CompleteJointMatterContactCorrection point)
          (completeJointActionMatchingContactPoint point) direction := by
  rw [matchingContactMatterCoordinates_eq_inputComp_add_correction]
  exact fieldDirectionalDerivative_add_matterCoordinates
    (fun localPoint =>
      matterCoordinateEquiv
        (InputActual.matter
          (canonicalSpatialContactTranslation
            (canonicalSpatialProjection point) localPoint)))
    (fixedP506L0CompleteJointMatterContactCorrection point)
    (inputMatterCoordinates_comp_translation_contDiff
      (canonicalSpatialProjection point))
    (fixedP506L0CompleteJointMatterContactCorrection_contDiff point)
    (completeJointActionMatchingContactPoint point) direction

private theorem inputMatterCoordinateDerivative_eq_matchingTranslation
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun localPoint =>
          matterCoordinateEquiv
            (InputActual.matter
              (canonicalSpatialContactTranslation
                (canonicalSpatialProjection point) localPoint)))
        (completeJointActionMatchingContactPoint point) direction =
      fieldDirectionalDerivative
        (fun candidate =>
          matterCoordinateEquiv (InputActual.matter candidate))
        point direction := by
  let field : BasePoint → MatterCoordinateCarrier :=
    fun candidate => matterCoordinateEquiv (InputActual.matter candidate)
  have translation :
      HasFDerivAt
        (canonicalSpatialContactTranslation (canonicalSpatialProjection point))
        (ContinuousLinearMap.id ℝ BasePoint)
        (completeJointActionMatchingContactPoint point) := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  have fieldDifferentiable :
      DifferentiableAt ℝ field point :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
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
        (field ∘
          canonicalSpatialContactTranslation (canonicalSpatialProjection point))
        (fderiv ℝ field point) (completeJointActionMatchingContactPoint point) := by
    have atTranslated :
        HasFDerivAt field (fderiv ℝ field point)
          (canonicalSpatialContactTranslation
            (canonicalSpatialProjection point)
            (completeJointActionMatchingContactPoint point)) := by
      simpa only [translatedPoint] using fieldDifferentiable.hasFDerivAt
    simpa using atTranslated.comp
      (completeJointActionMatchingContactPoint point) translation
  unfold fieldDirectionalDerivative
  have applied :=
    congrArg
      (fun derivative : BasePoint →L[ℝ] MatterCoordinateCarrier =>
        derivative (coordinateDirection direction))
      composed.fderiv
  simpa only [field, Function.comp_def] using applied

private theorem matterSectionCorrection_directionalDerivative
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        fixedP506L0CompleteJointMatterSectionCorrection point direction =
      canonicalTimeProjection (coordinateDirection direction) •
          fixedP506L0CompleteJointMatterSpatialResponseCoordinates
            (canonicalSpatialProjection point) +
        canonicalTimeProjection point •
          fderiv ℝ
              fixedP506L0CompleteJointMatterSpatialResponseCoordinates
              (canonicalSpatialProjection point)
            (canonicalSpatialProjection (coordinateDirection direction)) := by
  have responseDerivative :
      HasFDerivAt
        fixedP506L0CompleteJointMatterSpatialResponseCoordinates
        (fderiv ℝ
          fixedP506L0CompleteJointMatterSpatialResponseCoordinates
          (canonicalSpatialProjection point))
        (canonicalSpatialProjection point) :=
    (fixedP506L0CompleteJointMatterSpatialResponseCoordinates_contDiff
      |>.differentiable (by simp) |>.differentiableAt).hasFDerivAt
  have composedResponseDerivative :
      HasFDerivAt
        (fixedP506L0CompleteJointMatterSpatialResponseCoordinates ∘
          canonicalSpatialProjection)
        ((fderiv ℝ
          fixedP506L0CompleteJointMatterSpatialResponseCoordinates
          (canonicalSpatialProjection point)).comp
            canonicalSpatialProjection)
        point :=
    responseDerivative.comp point canonicalSpatialProjection.hasFDerivAt
  have correctionDerivative :=
    canonicalTimeProjection.hasFDerivAt.smul composedResponseDerivative
  have functionEquality :
      (fun candidate =>
        canonicalTimeProjection candidate •
          fixedP506L0CompleteJointMatterSpatialResponseCoordinates
            (canonicalSpatialProjection candidate)) =
        (fun candidate => canonicalTimeProjection candidate) •
          (fixedP506L0CompleteJointMatterSpatialResponseCoordinates ∘
            canonicalSpatialProjection) := by
    rfl
  unfold fieldDirectionalDerivative
    fixedP506L0CompleteJointMatterSectionCorrection
  rw [functionEquality]
  rw [correctionDerivative.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, Function.comp_apply]
  abel

private theorem matterContactCorrection_directionalDerivative
    (point localPoint : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fixedP506L0CompleteJointMatterContactCorrection point)
        localPoint direction =
      canonicalTimeProjection (coordinateDirection direction) •
        fixedP506L0CompleteJointMatterSpatialResponseCoordinates
          (canonicalSpatialProjection point) := by
  have derivative :=
    canonicalTimeProjection.hasFDerivAt
      (x := localPoint)
      |>.smul_const
        (fixedP506L0CompleteJointMatterSpatialResponseCoordinates
          (canonicalSpatialProjection point))
  have functionEquality :
      (fun candidate : BasePoint =>
        candidate canonicalLorentzianTimeDirection •
          fixedP506L0CompleteJointMatterSpatialResponseCoordinates
            (canonicalSpatialProjection point)) =
        fun candidate =>
          canonicalTimeProjection candidate •
            fixedP506L0CompleteJointMatterSpatialResponseCoordinates
              (canonicalSpatialProjection point) := by
    funext candidate
    rfl
  unfold fieldDirectionalDerivative
    fixedP506L0CompleteJointMatterContactCorrection
  rw [functionEquality]
  rw [derivative.fderiv]
  rfl

/-- Exact fixed-lineage primal assembly normal form.  It identifies the
complete matter-covariant seam with the first-jet mismatch of the two
action-generated response profiles; all primitive and connection terms
cancel on the same occurrence. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_matterCovariantDerivative_normalForm
    (point : BasePoint)
    (direction : LorentzianIndex) :
    matterCoordinateEquiv
        ((fixedP506L0CompleteJointActionSpacetimeAssemblySeam point
          ).matterCovariantDerivative direction) =
      fieldDirectionalDerivative
          fixedP506L0CompleteJointMatterSectionCorrection point direction -
        fieldDirectionalDerivative
          (fixedP506L0CompleteJointMatterContactCorrection point)
          (completeJointActionMatchingContactPoint point) direction := by
  have gravityAt :
      GlobalActual.gravityConnection point =
        (fixedP506L0CompleteJointActionMatchingContact point
          ).gravityConnection
          (completeJointActionMatchingContactPoint point) :=
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityConnection_at
      positiveSmoothUnifiedSource InputActual point
  have gaugeAt :
      GlobalActual.gaugeConnection point =
        (fixedP506L0CompleteJointActionMatchingContact point
          ).gaugeConnection
          (completeJointActionMatchingContactPoint point) :=
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection_at
      positiveSmoothUnifiedSource InputActual point
  have matterAt :
      GlobalActual.matter point =
        (fixedP506L0CompleteJointActionMatchingContact point).matter
          (completeJointActionMatchingContactPoint point) :=
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_matter_at
      positiveSmoothUnifiedSource InputActual point
  unfold fixedP506L0CompleteJointActionSpacetimeAssemblySeam
    completeJointActionJetAssemblySeam
    generatedDiracDualFormNativePointwiseActionJet
    toContinuumPointField
  simp only [Pi.sub_apply, map_sub]
  unfold holonomicMatterCovariantDerivative
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  rw [gravityAt, gaugeAt, matterAt,
    globalMatterCoordinateDerivative_normalForm,
    matchingContactMatterCoordinateDerivative_normalForm,
    inputMatterCoordinateDerivative_eq_matchingTranslation]
  abel

/-- The matter-covariant assembly seam is exactly the spatial derivative of
the source/action-generated response profile, weighted by physical time.
The temporal response of the global section and the matching contact cancels
on the same occurrence. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_matterCovariantDerivative_spatialProfile
    (point : BasePoint)
    (direction : LorentzianIndex) :
    matterCoordinateEquiv
        ((fixedP506L0CompleteJointActionSpacetimeAssemblySeam point
          ).matterCovariantDerivative direction) =
      canonicalTimeProjection point •
        fderiv ℝ
            fixedP506L0CompleteJointMatterSpatialResponseCoordinates
            (canonicalSpatialProjection point)
          (canonicalSpatialProjection (coordinateDirection direction)) := by
  rw [
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_matterCovariantDerivative_normalForm,
    matterSectionCorrection_directionalDerivative,
    matterContactCorrection_directionalDerivative]
  abel

/-- On the canonical Cauchy slice the global and matching-contact
matter-covariant first jets agree for every source-owned spatial contact. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_matterCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    (fixedP506L0CompleteJointActionSpacetimeAssemblySeam
      (canonicalCauchySlicePoint 0 space)).matterCovariantDerivative
        direction = 0 := by
  apply matterCoordinateEquiv.injective
  rw [
    fixedP506L0CompleteJointActionSpacetimeAssemblySeam_matterCovariantDerivative_spatialProfile]
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506MatterAssemblyNormalForm
