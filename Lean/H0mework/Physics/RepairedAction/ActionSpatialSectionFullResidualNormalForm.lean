import H0mework.Physics.RepairedAction.ActionSpatialSectionGaugeScalarNormalForm
import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterResidual

/-!
# Full residual normal form of the repaired spatial section

All nine coordinates below are evaluated on one fixed P506/L0
source/action-generated repaired section and one canonical slice point.  The
matter and conjugate-matter channels have already been proved zero.  The
coframe channel is exposed in the exact mother-action decomposition
`gauge + matter - constraint reaction`.

This complete carrier is diagnostic only.  No residual coordinate, sign,
support set, or zero-fiber witness is consumed by a successor constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionGaugeScalarNormalForm
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterResidual
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeLocalVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev RepairedActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private theorem repairedActual_coframe_one_zeroSlice
    (space : StageNineSpatialPoint) :
    RepairedActual.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  have jet := repairedSection_coframeFirstJet_zeroSlice space
  exact congrArg PointwiseLorentzianCoframeJet.coframe jet

private theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_physicalIIPlusCoframeTangent_smul
    (coframe variation : LorentzianCoframe) (parameter : ℝ) :
    physicalIIPlusCoframeTangent coframe (parameter • variation) =
      parameter • physicalIIPlusCoframeTangent coframe variation := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [physicalIIPlusCoframeTangent, coframeWedgeTangent,
      internalBivectorDual, lorentzianCoframeHodge,
      pairFirst, pairSecond] <;>
    ring

/-- Direct form-native `II+` reaction in the same continuous coframe-dual
carrier as the gauge and matter legs. -/
def
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeConstraintReactionCovector
    (space : StageNineSpatialPoint) :
    LorentzianCoframe →L[ℝ] ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  let field := toContinuumPointField RepairedActual point
  ({ toFun := fun variation =>
      formNativeCoframeConstraintReaction field variation
     map_add' := by
       intro first second
       unfold formNativeCoframeConstraintReaction
       rw [physicalIIPlusCoframeTangent_add,
         gravityTopologicalWedgeCoefficient_add_right]
     map_smul' := by
       intro parameter variation
       unfold formNativeCoframeConstraintReaction
       rw [
         fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_physicalIIPlusCoframeTangent_smul,
         gravityTopologicalWedgeCoefficient_smul_right]
       rfl } : LorentzianCoframe →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- Exact coframe residual of the already-generated repaired section. -/
def
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    LorentzianCoframe →L[ℝ] ℝ :=
  let point := canonicalCauchySlicePoint 0 space
  let field := toContinuumPointField RepairedActual point
  diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
      field +
    diracDualFormNativeCoframeMatterEulerCovector positiveSmoothUnifiedSource
      point field -
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeConstraintReactionCovector
      space

theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_coframe_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
      (canonicalCauchySlicePoint 0 space)).coframe =
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeResidualZeroSliceNormalForm
        space := by
  let point := canonicalCauchySlicePoint 0 space
  let field := toContinuumPointField RepairedActual point
  have nondegenerate : Matrix.det field.coframe ≠ 0 := by
    change Matrix.det
      (RepairedActual.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0
    rw [repairedActual_coframe_one_zeroSlice]
    norm_num
  change
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource
        point field =
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeResidualZeroSliceNormalForm
        space
  apply ContinuousLinearMap.ext
  intro variation
  rw [
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      positiveSmoothUnifiedSource point field nondegenerate variation]
  simp [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeResidualZeroSliceNormalForm,
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeConstraintReactionCovector,
    point, field]

/-! ## One complete carrier equality -/

def
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSixChannelResidualZeroSliceNormalForm
      space with
    matter := 0
    conjugateMatter := 0
    coframe :=
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionCoframeResidualZeroSliceNormalForm
        space }

/-- The complete section-level residual readout.  Its nine fields refer to
the same actual occurrence; the theorem constructs no next write. -/
theorem
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_zeroSlice_fullNormalForm
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidualSection
        (canonicalCauchySlicePoint 0 space) =
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm
        space := by
  have sixChannel :=
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_zeroSlice_sixChannelNormalForm
      space
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.gravityMultiplier
        sixChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.gravityAuxiliary
        sixChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeAuxiliary
        sixChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.lorentzConnection
        sixChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeConnection
        sixChannel
  · simpa [
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualZeroSliceNormalForm]
      using congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.scalar
        sixChannel
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_matter_zeroSlice
        space
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_conjugateMatter_zeroSlice
        space
  · exact
      fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_coframe_zeroSlice_normalForm
        space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionFullResidualNormalForm
