import H0mework.Physics.FullOccurrence.FixedAssemblySeamClosure

/-!
# Fixed P506/L0 full-occurrence global gravity/coframe verdict

The source/current-only full-occurrence operator has already generated one
global actual.  This module reads its two action coordinates whose contact
settlement can be changed by diagonal assembly.

The gravity-auxiliary residual is exactly the faithful variance-normalized
gravity-curvature difference between the global actual and its matching
action contact.  The coframe residual on the zero slice is exactly the joint
non-gravity load changed read; the topological BF curvature difference does
not enter it.  Both statements compare already generated action outputs and
neither residual is fed back into a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCoframeVerdict

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineBlockwiseConstitutive
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalResidualNormalForm
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceOriginSettlement
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeCoframeLocalVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev Global : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev Contact (point : BasePoint) : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact point

private abbrev GlobalField (point : BasePoint) : StageNineContinuumPointField :=
  toContinuumPointField Global point

private abbrev ContactField (point : BasePoint) : StageNineContinuumPointField :=
  toContinuumPointField (Contact point) 0

private theorem globalField_coframe_eq_contactField
    (point : BasePoint) :
    (GlobalField point).coframe = (ContactField point).coframe := by
  change Global.coframe point = (Contact point).coframe 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe_at
      Source Current point

private theorem globalField_gravityAuxiliary_eq_contactField
    (point : BasePoint) :
    (GlobalField point).gravityAuxiliary =
      (ContactField point).gravityAuxiliary := by
  change Global.gravityAuxiliary point = (Contact point).gravityAuxiliary 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary_at
      Source Current point

private theorem globalField_multiplier_eq_contactField
    (point : BasePoint) :
    (GlobalField point).gravitySimplicityMultiplier =
      (ContactField point).gravitySimplicityMultiplier := by
  change
    Global.gravitySimplicityMultiplier point =
      (Contact point).gravitySimplicityMultiplier 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_multiplier_at
      Source Current point

/-! ## Final gravity-auxiliary read -/

/-- On the generated global actual, the complete gravity-auxiliary residual
is exactly the faithful image of the already generated gravity-curvature
assembly difference.  The matching contact's native EC leg settles every
other term of the same `B` equation. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_gravityAuxiliary_normalForm
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Global point
      ).gravityAuxiliary =
      gravityInternalPairVarianceNormalization
        ((fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
          point).gravityCurvature) := by
  have contactZero :=
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_gravityAuxiliary_origin_zero
      point
  change
    formNativeGravityAuxiliaryEulerResidual (ContactField point) = 0
      at contactZero
  change
    formNativeGravityAuxiliaryEulerResidual (GlobalField point) =
      gravityInternalPairVarianceNormalization
        (holonomicGravityCurvature Global point -
          holonomicGravityCurvature (Contact point) 0)
  have auxiliaryEq :
      (GlobalField point).gravityAuxiliary =
        (ContactField point).gravityAuxiliary := by
    exact globalField_gravityAuxiliary_eq_contactField point
  have multiplierEq :
      (GlobalField point).gravitySimplicityMultiplier =
        (ContactField point).gravitySimplicityMultiplier := by
    exact globalField_multiplier_eq_contactField point
  unfold formNativeGravityAuxiliaryEulerResidual at contactZero ⊢
  change
    gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature (Contact point) 0) -
        gravityInternalDualEquiv (ContactField point).gravityAuxiliary +
        (ContactField point).gravitySimplicityMultiplier = 0
      at contactZero
  rw [auxiliaryEq, multiplierEq, map_sub]
  calc
    gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature Global point) -
        gravityInternalDualEquiv (ContactField point).gravityAuxiliary +
        (ContactField point).gravitySimplicityMultiplier =
      (gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature Global point) -
        gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature (Contact point) 0)) +
        (gravityInternalPairVarianceNormalization
            (holonomicGravityCurvature (Contact point) 0) -
          gravityInternalDualEquiv (ContactField point).gravityAuxiliary +
          (ContactField point).gravitySimplicityMultiplier) := by
        abel
    _ =
      gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature Global point) -
        gravityInternalPairVarianceNormalization
          (holonomicGravityCurvature (Contact point) 0) := by
        rw [contactZero, add_zero]

/-- Faithfulness of the variance normalization turns the preceding normal
form into an exact zero-fiber criterion. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_gravityAuxiliary_eq_zero_iff_gravityCurvatureSeam_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Global point
      ).gravityAuxiliary = 0 ↔
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
        point).gravityCurvature = 0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_gravityAuxiliary_normalForm]
  exact LinearEquiv.map_eq_zero_iff _

/-! ## Final zero-slice coframe read -/

private theorem global_coframe_one_zeroSlice
    (space : StageNineSpatialPoint) :
    Global.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Current).coframe (canonicalCauchySlicePoint 0 space) = 1
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice space

private theorem global_coframe_nondegenerate_zeroSlice
    (space : StageNineSpatialPoint) :
    Matrix.det
        ((GlobalField (canonicalCauchySlicePoint 0 space)).coframe) ≠ 0 := by
  rw [show
    (GlobalField (canonicalCauchySlicePoint 0 space)).coframe = 1 by
      exact global_coframe_one_zeroSlice space]
  simp

private theorem contact_coframe_nondegenerate_zeroSlice
    (space : StageNineSpatialPoint) :
    Matrix.det
        ((ContactField (canonicalCauchySlicePoint 0 space)).coframe) ≠ 0 := by
  rw [show
    (ContactField (canonicalCauchySlicePoint 0 space)).coframe =
        (GlobalField (canonicalCauchySlicePoint 0 space)).coframe by
      exact
        (globalField_coframe_eq_contactField
          (canonicalCauchySlicePoint 0 space)).symm]
  exact global_coframe_nondegenerate_zeroSlice space

/-- The final zero-slice coframe residual is the single joint changed read of
the gauge-plus-matter load.  The global and contact reactions are literally
the same generated primitive value, so no gravity-curvature seam occurs in
this equation. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_coframe_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Global
      (canonicalCauchySlicePoint 0 space)).coframe =
      (diracDualFormNativeCoframeGaugeEulerCovector Source
          (GlobalField (canonicalCauchySlicePoint 0 space)) +
        diracDualFormNativeCoframeMatterEulerCovector Source
          (canonicalCauchySlicePoint 0 space)
          (GlobalField (canonicalCauchySlicePoint 0 space))) -
      (diracDualFormNativeCoframeGaugeEulerCovector Source
          (ContactField (canonicalCauchySlicePoint 0 space)) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (ContactField (canonicalCauchySlicePoint 0 space))) := by
  let point := canonicalCauchySlicePoint 0 space
  have contactZero :=
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_coframe_origin_zero_zeroSlice
      space
  change
    diracDualFormNativeCoframeEulerCovector Source 0
        (ContactField point) = 0 at contactZero
  have reactionEq :
      formNativeCoframeConstraintReaction (GlobalField point) =
        formNativeCoframeConstraintReaction (ContactField point) := by
    funext variation
    unfold formNativeCoframeConstraintReaction
    rw [globalField_multiplier_eq_contactField,
      globalField_coframe_eq_contactField]
  change
    diracDualFormNativeCoframeEulerCovector Source point
        (GlobalField point) =
      (diracDualFormNativeCoframeGaugeEulerCovector Source
          (GlobalField point) +
        diracDualFormNativeCoframeMatterEulerCovector Source point
          (GlobalField point)) -
      (diracDualFormNativeCoframeGaugeEulerCovector Source
          (ContactField point) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (ContactField point))
  apply ContinuousLinearMap.ext
  intro variation
  have contactZeroAt := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ => covector variation)
    contactZero
  rw [
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      Source 0 (ContactField point)
      (contact_coframe_nondegenerate_zeroSlice space) variation]
    at contactZeroAt
  simp only [zero_apply] at contactZeroAt
  have contactLoadEqReaction :
      (diracDualFormNativeCoframeGaugeEulerCovector Source
            (ContactField point) +
          diracDualFormNativeCoframeMatterEulerCovector Source 0
            (ContactField point)) variation =
        formNativeCoframeConstraintReaction (ContactField point)
          variation := by
    exact sub_eq_zero.mp contactZeroAt
  have reactionEqAt := congrFun reactionEq variation
  rw [
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      Source point (GlobalField point)
      (global_coframe_nondegenerate_zeroSlice space) variation]
  simp only [sub_apply, add_apply]
  rw [reactionEqAt, ← contactLoadEqReaction]
  simp only [add_apply]

/-- Thus the remaining coframe zero-fiber question is exactly equality of
the two source/action-generated non-gravity loads, not vanishing of the
whole assembly seam and not a separate gravity-curvature condition. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_coframe_zeroSlice_eq_zero_iff_nonGravityLoad_eq_contact
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Global
      (canonicalCauchySlicePoint 0 space)).coframe = 0 ↔
      diracDualFormNativeCoframeGaugeEulerCovector Source
          (GlobalField (canonicalCauchySlicePoint 0 space)) +
        diracDualFormNativeCoframeMatterEulerCovector Source
          (canonicalCauchySlicePoint 0 space)
          (GlobalField (canonicalCauchySlicePoint 0 space)) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
          (ContactField (canonicalCauchySlicePoint 0 space)) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (ContactField (canonicalCauchySlicePoint 0 space)) := by
  rw [
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_coframe_zeroSlice_normalForm,
    sub_eq_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCoframeVerdict
