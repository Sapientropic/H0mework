import H0mework.Physics.IdentityHessian.CartanECNormalPrimitiveDiagonalActual
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermFixedContactReadout
import H0mework.Physics.MatterPreparation.ContorsionCoherentMatterNormalForm

/-!
# Fixed P506/L0 matter-joint regularity

This module expands only the primal and adjoint affine germs consumed by the
KIN-6 Cartan response.  It is fixed to the P506/L0 source-generated `U*`
Cauchy restriction and does not state regularity for an arbitrary current.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCoframeScalarMatterRegularity
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterAdjointRegularity
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentMatterNormalForm

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

theorem canonicalZeroSlice_contDiff :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show canonicalCauchySlicePoint 0 =
      fun space =>
        EuclideanSpace.single canonicalLorentzianTimeDirection 0 +
          canonicalSpatialInclusion space by
    funext space
    exact canonicalCauchySlicePoint_eq_const_add_inclusion 0 space]
  exact contDiff_const.add canonicalSpatialInclusion.contDiff

private theorem fixedP286GaussCauchyState_conjugateMatter_constant :
    positiveP506MatterCurrentP286GaussCauchyState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_conjugateMatter,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugateMatter,
    positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentLinearPlebanskiCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact
    actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
      positiveP506MatterCurrentLinearPlebanskiCauchyState 0
      diracSpinZeroMatterCoordinate
      currentLinearPlebanskiCauchyState_conjugate_allSpace space

private theorem fixedLorentzResponseCauchyState_conjugateMatter_constant :
    positiveP506MatterCurrentLorentzResponseCauchyState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact
    actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
      positiveP506MatterCurrentP286GaussCauchyState
      positiveP506MatterCurrentP286AxisContact
      diracSpinZeroMatterCoordinate
      fixedP286GaussCauchyState_conjugateMatter_constant space

theorem fixedCurrent_matter_constant :
    positiveP506MatterCurrentFullSynchronizedCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact
    actionGeneratedMatterLocalField_zeroSlice_of_constant
      positiveP506MatterCurrentLorentzResponseCauchyState 0
      diracSpinTwoMatterProbe
      lorentzResponseCauchyState_matter_constant_local space

theorem fixedCurrent_conjugateMatter_constant :
    positiveP506MatterCurrentFullSynchronizedCauchyState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact
    actionGeneratedConjugateMatterLocalField_zeroSlice_of_constant
      positiveP506MatterCurrentLorentzResponseCauchyState 0
      diracSpinZeroMatterCoordinate
      fixedLorentzResponseCauchyState_conjugateMatter_constant space

private theorem uStar_smooth :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.Smooth :=
  positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth

theorem fixedMatterRawVelocity_coordinates_contDiff :
    ContDiff ℝ ∞ fun space =>
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity
          positiveP506MatterCurrentFullSynchronizedCauchyState space) := by
  change ContDiff ℝ ∞ fun space =>
    matterCoordinateEquiv
      (actionGeneratedMatterRawTimeVelocity
        (canonicalCauchyRestriction 0
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
        space)
  rw [show
    (fun space =>
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity
          (canonicalCauchyRestriction 0
            positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
          space)) =
      fun space =>
        matterCoordinateEquiv
          (holonomicIdentityCoframeMatterRawTimeVelocity
            positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
            (canonicalCauchySlicePoint 0 space)) by
    funext space
    rw [
      actionGeneratedMatterRawTimeVelocity_canonicalCauchyRestriction
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        uStar_smooth]]
  exact
    (holonomicIdentityCoframeMatterRawTimeVelocity_coordinate_contDiff
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
      uStar_smooth).comp canonicalZeroSlice_contDiff

theorem fixedMatterSpatialDerivativeCoordinate_zero
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    cauchyMatterSpatialDerivativeCoordinate
        positiveP506MatterCurrentFullSynchronizedCauchyState space direction =
      0 := by
  unfold cauchyMatterSpatialDerivativeCoordinate
  rw [fixedCurrent_matter_constant]
  simp

theorem fixedConjugateMatterSpatialDerivative_zero
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    cauchyConjugateMatterSpatialDerivative
        positiveP506MatterCurrentFullSynchronizedCauchyState space direction =
      0 := by
  unfold cauchyConjugateMatterSpatialDerivative
    cauchyConjugateMatterSpatialDerivativeCoordinate
  rw [fixedCurrent_conjugateMatter_constant]
  simp

theorem fixedConjugateMatterTimeDerivative_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun space =>
      actionGeneratedConjugateMatterTimeDerivative
        positiveP506MatterCurrentFullSynchronizedCauchyState space matter := by
  unfold positiveP506MatterCurrentFullSynchronizedCauchyState
  rw [show
    (fun space =>
      actionGeneratedConjugateMatterTimeDerivative
        (canonicalCauchyRestriction 0
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
        space matter) =
      fun space =>
        holonomicIdentityCoframeConjugateMatterActionVelocity
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          (canonicalCauchySlicePoint 0 space) matter by
    funext space
    rw [
      actionGeneratedConjugateMatterTimeDerivative_canonicalCauchyRestriction
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        uStar_smooth]]
  exact
    (holonomicIdentityCoframeConjugateMatterActionVelocity_apply_contDiff
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
      uStar_smooth matter).comp canonicalZeroSlice_contDiff

theorem fixedJointMatterCoordinates_normalForm
    (space : StageNineSpatialPoint) (point : BasePoint) :
    matterCoordinateEquiv
        ((sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space).matter point) =
      matterCoordinateEquiv diracSpinTwoMatterProbe +
        point canonicalLorentzianTimeDirection •
          matterCoordinateEquiv
            (actionGeneratedMatterRawTimeVelocity
              positiveP506MatterCurrentFullSynchronizedCauchyState space) := by
  change
    matterCoordinateEquiv
        (actionGeneratedMatterLocalField
          positiveP506MatterCurrentFullSynchronizedCauchyState space point) =
      _
  unfold actionGeneratedMatterLocalField
    actionGeneratedMatterLocalCoordinate
  rw [fixedCurrent_matter_constant]
  simp only [matterCoordinateEquiv.apply_symm_apply]
  unfold actionGeneratedMatterLocalIncrement
  rw [Fin.sum_univ_four]
  have h0 :
      actionGeneratedMatterLocalJetCoordinate
          positiveP506MatterCurrentFullSynchronizedCauchyState space 0 =
        matterCoordinateEquiv
          (actionGeneratedMatterRawTimeVelocity
            positiveP506MatterCurrentFullSynchronizedCauchyState space) :=
    rfl
  have h1 :
      actionGeneratedMatterLocalJetCoordinate
          positiveP506MatterCurrentFullSynchronizedCauchyState space 1 = 0 := by
    exact fixedMatterSpatialDerivativeCoordinate_zero space 0
  have h2 :
      actionGeneratedMatterLocalJetCoordinate
          positiveP506MatterCurrentFullSynchronizedCauchyState space 2 = 0 := by
    exact fixedMatterSpatialDerivativeCoordinate_zero space 1
  have h3 :
      actionGeneratedMatterLocalJetCoordinate
          positiveP506MatterCurrentFullSynchronizedCauchyState space 3 = 0 := by
    exact fixedMatterSpatialDerivativeCoordinate_zero space 2
  rw [h0, h1, h2, h3]
  simp only [add_apply,
    ContinuousLinearMap.smulRight_apply, localBaseCoordinate_apply,
    smul_zero, add_zero]
  rfl

theorem fixedJointMatterCoordinates_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv
        ((sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          joint.1).matter joint.2) := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv
        ((sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          joint.1).matter joint.2)) =
      fun joint =>
        matterCoordinateEquiv diracSpinTwoMatterProbe +
          joint.2 canonicalLorentzianTimeDirection •
            matterCoordinateEquiv
              (actionGeneratedMatterRawTimeVelocity
                positiveP506MatterCurrentFullSynchronizedCauchyState
                joint.1) by
    funext joint
    exact fixedJointMatterCoordinates_normalForm joint.1 joint.2]
  have timeSmooth : ContDiff ℝ ∞
      (fun joint : StageNineSpatialPoint × BasePoint =>
        joint.2 canonicalLorentzianTimeDirection) := by
    fun_prop
  exact contDiff_const.add
    (timeSmooth.smul
      (fixedMatterRawVelocity_coordinates_contDiff.comp contDiff_fst))

theorem fixedJointConjugateMatter_apply_normalForm
    (space : StageNineSpatialPoint) (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space).conjugateMatter point matter =
      diracSpinZeroMatterCoordinate matter +
        point canonicalLorentzianTimeDirection •
          actionGeneratedConjugateMatterTimeDerivative
            positiveP506MatterCurrentFullSynchronizedCauchyState
            space matter := by
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space point matter =
      _
  unfold actionGeneratedConjugateMatterLocalField
  rw [fixedCurrent_conjugateMatter_constant]
  rw [Fin.sum_univ_four]
  have h0 :
      actionGeneratedConjugateMatterLocalJet
          positiveP506MatterCurrentFullSynchronizedCauchyState space 0 =
        actionGeneratedConjugateMatterTimeDerivative
          positiveP506MatterCurrentFullSynchronizedCauchyState space :=
    rfl
  have h1 :
      actionGeneratedConjugateMatterLocalJet
          positiveP506MatterCurrentFullSynchronizedCauchyState space 1 = 0 := by
    exact fixedConjugateMatterSpatialDerivative_zero space 0
  have h2 :
      actionGeneratedConjugateMatterLocalJet
          positiveP506MatterCurrentFullSynchronizedCauchyState space 2 = 0 := by
    exact fixedConjugateMatterSpatialDerivative_zero space 1
  have h3 :
      actionGeneratedConjugateMatterLocalJet
          positiveP506MatterCurrentFullSynchronizedCauchyState space 3 = 0 := by
    exact fixedConjugateMatterSpatialDerivative_zero space 2
  rw [h0, h1, h2, h3]
  simp only [smul_zero, add_zero, localBaseCoordinate_apply]
  rfl

theorem fixedJointConjugateMatter_apply_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1).conjugateMatter joint.2 matter := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1).conjugateMatter joint.2 matter) =
      fun joint =>
        diracSpinZeroMatterCoordinate matter +
          joint.2 canonicalLorentzianTimeDirection •
            actionGeneratedConjugateMatterTimeDerivative
              positiveP506MatterCurrentFullSynchronizedCauchyState
              joint.1 matter by
    funext joint
    exact fixedJointConjugateMatter_apply_normalForm
      joint.1 joint.2 matter]
  have timeSmooth : ContDiff ℝ ∞
      (fun joint : StageNineSpatialPoint × BasePoint =>
        joint.2 canonicalLorentzianTimeDirection) := by
    fun_prop
  exact contDiff_const.add
    (timeSmooth.smul
      (fixedConjugateMatterTimeDerivative_apply_contDiff matter
        |>.comp contDiff_fst))

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
