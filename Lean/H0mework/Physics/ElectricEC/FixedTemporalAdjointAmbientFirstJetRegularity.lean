import H0mework.Physics.TimePrimitive.FirstAmbientJetRegularity
import H0mework.Physics.JointVariation.AdjointTemporalLocalRegularity
import H0mework.Physics.ElectricEC.FixedOriginTransport
import H0mework.Physics.ElectricJoint.FixedOriginCoframeClosure
import H0mework.Physics.Jets.CanonicalTimePrimitiveMeasurableGermCalculus

/-!
# Fixed P506/L0 live-electric EC temporal adjoint ambient first jet

The complete-joint adjoint correction is continuous at every fixed-lineage
zero-slice occurrence.  Its source-free canonical primitive therefore has the
ambient first derivative selected by the same action profile.  This identifies
the full first jet of the adjoint field already carried by the later
live-electric Einstein--Cartan current.

This module transports the existing source/action write.  It accepts no
residual, target jet, zero-fiber receipt, branch, or free coefficient.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalAdjointAmbientFirstJetRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalTimePrimitiveMeasurableGermCalculus
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source Input

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

/-- Fixed recentered U5 adjoint coordinates at one zero-slice occurrence. -/
def fixedP506L0CompleteJointRecenteredAdjointCoordinates
    (space : StageNineSpatialPoint) : BasePoint → MatterCoordinateCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  fun localPoint =>
    holonomicConjugateMatterCoordinates
      (fullyRecenterHolonomicConfiguration
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual point)
      localPoint

/-- Fixed input adjoint coordinates in the same recentered chart. -/
def fixedP506L0CompleteJointRecenteredInputAdjointCoordinates
    (space : StageNineSpatialPoint) : BasePoint → MatterCoordinateCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  holonomicConjugateMatterCoordinates
      FixedP506FormNativeJointActionSolvedSuccessor ∘
    canonicalSpacetimeContactTranslation point

/-- The canonical primitive of the action-owned adjoint correction in that
same recentered chart. -/
def fixedP506L0CompleteJointRecenteredAdjointPrimitive
    (space : StageNineSpatialPoint) : BasePoint → MatterCoordinateCarrier :=
  let point := canonicalCauchySlicePoint 0 space
  canonicalTimePrimitive
      (completeJointAdjointTemporalCoordinateCorrection
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor) ∘
    canonicalSpacetimeContactTranslation point

/-- The named recentered coordinates are exactly the global U5 adjoint field
composed with the occurrence translation. -/
theorem fixedP506L0CompleteJointRecenteredAdjointCoordinates_eq_comp
    (space : StageNineSpatialPoint) :
    fixedP506L0CompleteJointRecenteredAdjointCoordinates space =
      holonomicConjugateMatterCoordinates
          fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) := by
  unfold fixedP506L0CompleteJointRecenteredAdjointCoordinates
  dsimp only
  unfold holonomicConjugateMatterCoordinates
  rw [fullyRecenterHolonomicConfiguration_conjugateMatter]
  rfl

private theorem canonicalSpacetimeContactTranslation_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

/-- The fixed complete-joint adjoint correction is continuous at every point
of the canonical zero slice. -/
theorem fixedP506L0CompleteJointAdjointTemporalCorrection_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection Source Input)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeAtPoint : Input.coframe point = 1 := by
    simpa only [point] using
      fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have nondegenerate : Matrix.det (Input.coframe point) ≠ 0 := by
    rw [coframeAtPoint]
    simp
  have noncharacteristic :
      coframeTemporalPrincipalScalar (Input.coframe point) ≠ 0 := by
    rw [coframeAtPoint, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  exact
    completeJointAdjointTemporalCoordinateCorrection_contDiffAt
      Source Input fixedP506FormNativeJointActionSolvedSuccessor_smooth point
      nondegenerate noncharacteristic

/-- Recentring preserves continuity of the fixed adjoint action profile at
the matching occurrence. -/
theorem
    fixedP506L0CompleteJointAdjointTemporalCorrection_recentered_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection Source Input ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have profileAtPoint :
      ContDiffAt ℝ 0
        (completeJointAdjointTemporalCoordinateCorrection Source Input)
        point :=
    fixedP506L0CompleteJointAdjointTemporalCorrection_contDiffAt_zeroSlice
      space
  have translationRegular :
      ContDiffAt ℝ 0 (canonicalSpacetimeContactTranslation point) 0 :=
    (canonicalSpacetimeContactTranslation_contDiff point).contDiffAt.of_le
      (by decide)
  have profileAtTranslated :
      ContDiffAt ℝ 0
        (completeJointAdjointTemporalCoordinateCorrection Source Input)
        (canonicalSpacetimeContactTranslation point 0) := by
    simpa [canonicalSpacetimeContactTranslation] using profileAtPoint
  have composed := profileAtTranslated.comp 0 translationRegular
  simpa [point] using composed

/-- The recentered canonical primitive has the exact ambient derivative
selected by the fixed adjoint action profile. -/
theorem
    fixedP506L0CompleteJointAdjointTemporalPrimitive_recentered_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (fixedP506L0CompleteJointRecenteredAdjointPrimitive space)
      (canonicalTimeProjection.smulRight
        (completeJointAdjointTemporalCoordinateCorrection Source Input
          (canonicalCauchySlicePoint 0 space)))
      0 := by
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  unfold fixedP506L0CompleteJointRecenteredAdjointPrimitive
  rw [show
    canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Input) ∘
        translation =
      canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source Input ∘
          translation) by
    simpa [translation, point] using
      canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
        (completeJointAdjointTemporalCoordinateCorrection Source Input) space]
  have generated :=
    canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
      (completeJointAdjointTemporalCoordinateCorrection Source Input ∘
        translation)
      (fixedP506L0CompleteJointAdjointTemporalCorrection_recentered_contDiffAt
        space)
  simpa [translation, point, canonicalSpacetimeContactTranslation] using
    generated

/-- The already generated adjoint primitive is locally continuous on the
recentered carrier.  This is the value regularity consumed by the Cartan spin
response in the next action sweep. -/
theorem
    fixedP506L0CompleteJointAdjointTemporalPrimitive_recentered_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 0
      (fixedP506L0CompleteJointRecenteredAdjointPrimitive space) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  unfold fixedP506L0CompleteJointRecenteredAdjointPrimitive
  rw [show
    canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Input) ∘
        translation =
      canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source Input ∘
          translation) by
    simpa [translation, point] using
      canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
        (completeJointAdjointTemporalCoordinateCorrection Source Input) space]
  exact
    canonicalTimePrimitive_contDiffAt_zero_of_contDiffAt_zero
      (completeJointAdjointTemporalCoordinateCorrection Source Input ∘
        translation)
      (fixedP506L0CompleteJointAdjointTemporalCorrection_recentered_contDiffAt
        space)

private theorem current_conjugateMatter_eq_temporal :
    Current.conjugateMatter = Temporal.conjugateMatter := by
  calc
    Current.conjugateMatter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing
    _ = Temporal.conjugateMatter := by
      rfl

/-- Exact field normal form of the already generated U5 adjoint write after
recentring at a fixed zero-slice occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_conjugateMatterCoordinates_normalForm
    (space : StageNineSpatialPoint) :
    fixedP506L0CompleteJointRecenteredAdjointCoordinates space =
      fixedP506L0CompleteJointRecenteredInputAdjointCoordinates space +
        fixedP506L0CompleteJointRecenteredAdjointPrimitive space := by
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  unfold fixedP506L0CompleteJointRecenteredAdjointCoordinates
    fixedP506L0CompleteJointRecenteredInputAdjointCoordinates
    fixedP506L0CompleteJointRecenteredAdjointPrimitive
  dsimp only
  unfold holonomicConjugateMatterCoordinates
  rw [fullyRecenterHolonomicConfiguration_conjugateMatter,
    current_conjugateMatter_eq_temporal,
    completeJointGlobalTemporalCurrent_conjugateMatter]
  funext localPoint
  simp only [Pi.add_apply, Function.comp_apply, matterDualCoordinates_add,
    matterDualCoordinates_matterDualOfCoordinates]

/-- The literal U5 adjoint coordinates are locally continuous after
recentring at every fixed-lineage zero-slice occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_conjugateMatterCoordinates_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 0
      (fixedP506L0CompleteJointRecenteredAdjointCoordinates space) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have translationSmooth :
      ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) :=
    canonicalSpacetimeContactTranslation_contDiff point
  have inputSmooth : ContDiff ℝ ∞
      (fixedP506L0CompleteJointRecenteredInputAdjointCoordinates space) := by
    unfold fixedP506L0CompleteJointRecenteredInputAdjointCoordinates
    exact
      (holonomicConjugateMatterCoordinates_contDiff Input
        fixedP506FormNativeJointActionSolvedSuccessor_smooth).comp
          translationSmooth
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_conjugateMatterCoordinates_normalForm]
  exact (inputSmooth.contDiffAt.of_le (by norm_num)).add
    (fixedP506L0CompleteJointAdjointTemporalPrimitive_recentered_contDiffAt
      space)

/-- The fixed input adjoint field has its ordinary ambient derivative in the
same recentered chart. -/
theorem fixedP506L0CompleteJointRecenteredInputAdjointCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (fixedP506L0CompleteJointRecenteredInputAdjointCoordinates space)
      (fderiv ℝ
        (fixedP506L0CompleteJointRecenteredInputAdjointCoordinates space) 0)
      0 := by
  let point := canonicalCauchySlicePoint 0 space
  have translationSmooth :
      ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) :=
    canonicalSpacetimeContactTranslation_contDiff point
  have inputSmooth : ContDiff ℝ ∞
      (fixedP506L0CompleteJointRecenteredInputAdjointCoordinates space) := by
    unfold fixedP506L0CompleteJointRecenteredInputAdjointCoordinates
    exact
      (holonomicConjugateMatterCoordinates_contDiff Input
        fixedP506FormNativeJointActionSolvedSuccessor_smooth).comp
          translationSmooth
  exact inputSmooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt

/-- The complete ambient first derivative of the fixed U5 adjoint coordinates
is the input first derivative plus the source/action-generated canonical-time
correction at the same occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_conjugateMatterCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (fixedP506L0CompleteJointRecenteredAdjointCoordinates space)
      (fderiv ℝ
          (fixedP506L0CompleteJointRecenteredInputAdjointCoordinates space) 0 +
        canonicalTimeProjection.smulRight
          (completeJointAdjointTemporalCoordinateCorrection Source Input
            (canonicalCauchySlicePoint 0 space)))
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_conjugateMatterCoordinates_normalForm]
  exact
    (fixedP506L0CompleteJointRecenteredInputAdjointCoordinates_hasFDerivAt
      space).add
      (fixedP506L0CompleteJointAdjointTemporalPrimitive_recentered_hasFDerivAt
        space)

/-- The recentered first derivative gives ordinary ambient differentiability
of the same U5 adjoint field at the matching zero-slice occurrence.  The
inverse translation is only a chart transporter; no target jet or residual is
added. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatterCoordinates_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  let recentered := fixedP506L0CompleteJointRecenteredAdjointCoordinates space
  let inverseTranslation := canonicalSpacetimeContactTranslation (-point)
  have recenteredDifferentiable : DifferentiableAt ℝ recentered 0 := by
    exact
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_conjugateMatterCoordinates_hasFDerivAt
        space).differentiableAt
  have inverseTranslationDifferentiable : DifferentiableAt ℝ
      inverseTranslation point := by
    unfold inverseTranslation canonicalSpacetimeContactTranslation
    fun_prop
  have inverseTranslationPoint : inverseTranslation point = 0 := by
    unfold inverseTranslation canonicalSpacetimeContactTranslation
    simp
  have recenteredAtInverse : DifferentiableAt ℝ recentered
      (inverseTranslation point) := by
    rw [inverseTranslationPoint]
    exact recenteredDifferentiable
  have ambientEquality :
      holonomicConjugateMatterCoordinates Current =
        recentered ∘ inverseTranslation := by
    unfold recentered
    rw [fixedP506L0CompleteJointRecenteredAdjointCoordinates_eq_comp]
    funext candidate
    unfold inverseTranslation canonicalSpacetimeContactTranslation point
    simp
  rw [ambientEquality]
  exact
    recenteredAtInverse.comp point inverseTranslationDifferentiable

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalAdjointAmbientFirstJetRegularity
