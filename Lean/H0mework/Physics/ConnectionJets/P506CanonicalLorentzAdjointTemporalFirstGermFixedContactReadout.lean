import H0mework.Physics.Matter.MatterActionTimeVelocity
import H0mework.Physics.MatterCurrent.FullSynchronizedResponseLocalActualLift
import H0mework.Physics.MatterCurrent.P286CompleteActionPrincipalFullNonlinearLocalActualLift

/-!
# C3h197: fixed P506/L0 contact readout

This dependency-light layer exposes only the already generated contact fields
needed to compare the fresh C3h187 stress input.  Numerical stress paths and
their large coordinate proofs live in the successor stress module.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

theorem matterResponseOrigin_scalar_eq_vacuum :
    positiveP506MatterCurrentMatterResponseOriginField.scalar =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    positiveP506MatterCurrentMatterResponseLocalActualLift.scalar 0 = _
  rw [positiveP506MatterCurrentMatterResponseLocalActualLift_scalar,
    positiveP506MatterCurrentLorentzResponseLocalActualLift_scalar]
  rw [
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.1,
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum]

theorem matterResponseOrigin_scalarCovariantDerivative_zero :
    positiveP506MatterCurrentMatterResponseOriginField.scalarCovariantDerivative =
      0 := by
  funext direction
  change
    holonomicScalarCovariantDerivative
        positiveP506MatterCurrentMatterResponseLocalActualLift 0 direction = 0
  unfold holonomicScalarCovariantDerivative
  rw [positiveP506MatterCurrentMatterResponseLocalActualLift_scalar,
    positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeConnection,
    positiveP506MatterCurrentLorentzResponseLocalActualLift_scalar,
    positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeConnection,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.1,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.1]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_origin_zero
      direction

theorem matterResponseOrigin_matter_probe :
    positiveP506MatterCurrentMatterResponseOriginField.matter =
      diracSpinTwoMatterProbe := by
  change
    positiveP506MatterCurrentMatterResponseLocalActualLift.matter 0 = _
  rw [positiveP506MatterCurrentMatterResponseLocalActualLift_matter_origin]
  change positiveP506MatterCurrentCompleteBaseActual.matter 0 = _
  rw [
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.1]
  exact currentU7_matter_origin

theorem matterResponseOrigin_conjugate_probe :
    positiveP506MatterCurrentMatterResponseOriginField.conjugateMatter =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter 0 = _
  rw [positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin]
  change positiveP506MatterCurrentCompleteBaseActual.conjugateMatter 0 = _
  rw [
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.2]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin

theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

@[simp] theorem matterResponseLocalActualLift_matterField :
    positiveP506MatterCurrentMatterResponseLocalActualLift.matter =
      actionGeneratedMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0 :=
  rfl

theorem matterResponseLocalActualLift_gravityConnection_origin_eq_cauchy :
    positiveP506MatterCurrentMatterResponseLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentLorentzResponseCauchyState.gravityConnection 0 := by
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
        (canonicalCauchySlicePoint 0 0)
  rw [canonicalCauchySlicePoint_zero_zero_local]

theorem matterResponseLocalActualLift_gaugeConnection_origin_eq_cauchy :
    positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeConnection 0 =
      positiveP506MatterCurrentLorentzResponseCauchyState.gaugeConnection 0 := by
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection 0 =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection
        (canonicalCauchySlicePoint 0 0)
  rw [canonicalCauchySlicePoint_zero_zero_local]

theorem currentP286GaussCauchyState_matter_constant_local :
    positiveP506MatterCurrentP286GaussCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentLinearPlebanskiCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentLinearPlebanskiCauchyState 0
    diracSpinTwoMatterProbe currentLinearPlebanskiCauchyState_matter_allSpace
    space

theorem lorentzResponseCauchyState_matter_constant_local :
    positiveP506MatterCurrentLorentzResponseCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentP286GaussCauchyState
    positiveP506MatterCurrentP286AxisContact diracSpinTwoMatterProbe
    currentP286GaussCauchyState_matter_constant_local space

theorem completeBaseActual_gaugeConnection_origin_zero :
    positiveP506MatterCurrentCompleteBaseActual.gaugeConnection 0 = 0 := by
  rw [
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.1]
  funext direction
  apply p286CoordinateEquiv.injective
  have coordinateForm := congrFun
    (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm
      0) direction
  simpa [holonomicP286GaugeConnectionCoordinate,
    c3h181U7ConnectionNormalForm] using coordinateForm

theorem lorentzResponseCauchyState_gaugeConnection_origin_zero_local :
    positiveP506MatterCurrentLorentzResponseCauchyState.gaugeConnection 0 = 0 := by
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection
        (canonicalCauchySlicePoint 0 0) = 0
  rw [canonicalCauchySlicePoint_zero_zero_local]
  change positiveP506MatterCurrentCompleteBaseActual.gaugeConnection 0 = 0
  exact completeBaseActual_gaugeConnection_origin_zero

end


end
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
