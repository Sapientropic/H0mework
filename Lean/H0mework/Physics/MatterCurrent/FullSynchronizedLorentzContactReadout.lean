import H0mework.Physics.SynchronizedJoint.MatterReadout
import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzActualOriginCoframeAction
import H0mework.Physics.MatterPreparation.ContorsionCoherentP286BFMomentumBridge
import H0mework.Physics.MatterPreparation.ContorsionFreshScalarConstraint

/-!
# C3h207a: latest-current Lorentz contact readout

C3h203 generated the latest full-synchronized Lorentz actual.  Before
computing its surviving temporal-Gauss sectors, this module exposes the exact
matter contact consumed by that computation:

```text
C3h200n current
→ source/action base actual
→ Einstein--Cartan synchronized matter Cauchy state
→ C3h203 judged actual origin.
```

The equalities below are shallow projections of the existing forward
producer graph.  They neither identify the latest current with the older
Stable carrier nor assert equality of their whole non-gravity projections.
In particular, the latest gauge auxiliary contact is allowed to differ from
the old fixed contact.  No obstruction value, zero certificate, residual
inverse, repair coefficient, branch, or stationarity receipt is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzContactReadout

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeNonGravityContactProjection
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalFullActionCoherentDiagonalActual
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEinsteinCartanSpinContorsionAction
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineCurrentFullSynchronizedLorentzMatterReadout
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentCartanActual
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzActualOriginCoframeAction
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileCurrentResponse
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshCoherentP286BFMomentumBridge
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzFreshScalarConstraint
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Public shallow aliases of the existing producer graph -/

abbrev positiveP506MatterCurrentFullSynchronizedLorentzBaseActual :
    StageNineHolonomicConfiguration :=
  currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
    PreContorsionFullLorentzTriangularCurrent 0

abbrev positiveP506MatterCurrentFullSynchronizedMatterCauchyState :
    StageNineCauchyState :=
  fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual

/-! ## Dependency-light zero-slice helpers -/

private theorem matterLocalField_zeroSlice_of_constant
    (state : StageNineCauchyState)
    (anchor : StageNineSpatialPoint)
    (target : DiracExteriorMatterCarrier)
    (stateMatter : state.matter = fun _ => target)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterLocalField state anchor
        (canonicalCauchySlicePoint 0 space) = target := by
  have spatialDerivativeZero (direction : Fin 3) :
      cauchyMatterSpatialDerivativeCoordinate state anchor direction = 0 := by
    unfold cauchyMatterSpatialDerivativeCoordinate
    rw [stateMatter]
    simp
  apply matterCoordinateEquiv.injective
  simp [actionGeneratedMatterLocalField,
    actionGeneratedMatterLocalCoordinate,
    actionGeneratedMatterLocalIncrement,
    actionGeneratedMatterLocalJetCoordinate,
    stateMatter, spatialDerivativeZero,
    canonicalCauchySlicePoint, Fin.sum_univ_four]

private theorem conjugateMatterLocalField_zeroSlice_of_constant
    (state : StageNineCauchyState)
    (anchor : StageNineSpatialPoint)
    (target : Module.Dual ℂ DiracExteriorMatterCarrier)
    (stateConjugate : state.conjugateMatter = fun _ => target)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterLocalField state anchor
        (canonicalCauchySlicePoint 0 space) = target := by
  have spatialDerivativeZero (direction : Fin 3) :
      cauchyConjugateMatterSpatialDerivativeCoordinate state anchor direction =
        0 := by
    unfold cauchyConjugateMatterSpatialDerivativeCoordinate
    rw [stateConjugate]
    simp
  unfold actionGeneratedConjugateMatterLocalField
  rw [stateConjugate]
  simp [canonicalCauchySlicePoint,
    actionGeneratedConjugateMatterLocalJet,
    cauchyConjugateMatterSpatialDerivative,
    spatialDerivativeZero, Fin.sum_univ_four]

/-! ## Latest-current primitive matter contact -/

theorem preContorsionFullLorentzTriangularCurrent_matter_constant :
    PreContorsionFullLorentzTriangularCurrent.matter =
      fun _ => diracSpinTwoMatterProbe := by
  rw [preContorsionFullLorentzTriangularCurrent_matter_eq_profile]
  funext space
  unfold PreContorsionSpatialProfileCurrent canonicalCauchyRestriction
  rw [preContorsionSpatialProfileActual_retains_matterFields.1]
  change
    actionGeneratedMatterLocalField positiveSourceTargetMatterCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact matterLocalField_zeroSlice_of_constant
    positiveSourceTargetMatterCauchyState 0 diracSpinTwoMatterProbe
    (by
      funext candidate
      exact positiveSourceTargetMatterCauchyState_matter)
    space

theorem preContorsionFullLorentzTriangularCurrent_conjugateMatter_constant :
    PreContorsionFullLorentzTriangularCurrent.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  rw [preContorsionFullLorentzTriangularCurrent_conjugateMatter_eq_profile]
  funext space
  unfold PreContorsionSpatialProfileCurrent canonicalCauchyRestriction
  rw [preContorsionSpatialProfileActual_retains_matterFields.2]
  change
    actionGeneratedConjugateMatterLocalField positiveSourceTargetMatterCauchyState
        0 (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact conjugateMatterLocalField_zeroSlice_of_constant
    positiveSourceTargetMatterCauchyState 0
    (diracSpinZeroMatterCoordinate :
      Module.Dual ℂ DiracExteriorMatterCarrier)
    (by
      funext candidate
      simpa [positiveSourceTargetMatterCauchyState,
        sourceTargetMatterCauchyState] using
        positiveSourceTargetMatterCauchyState_conjugate)
    space

/-! ## Synchronized matter Cauchy contact -/

theorem
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_origin :
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState.matter 0 =
      diracSpinTwoMatterProbe := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  unfold positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual).matter
        (canonicalCauchySlicePoint 0 0) =
      diracSpinTwoMatterProbe
  rw [contactZero]
  change
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual.matter 0 =
      diracSpinTwoMatterProbe
  rw [show
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual =
        currentFullSynchronizedCompleteP286BaseActual
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent 0 by rfl,
    currentFullSynchronizedCompleteP286BaseActual_matter_origin]
  exact congrFun
    preContorsionFullLorentzTriangularCurrent_matter_constant 0

theorem
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_conjugateMatter_origin :
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState.conjugateMatter
        0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  unfold positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual
      ).conjugateMatter (canonicalCauchySlicePoint 0 0) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [contactZero]
  change
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual.conjugateMatter
        0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [show
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual =
        currentFullSynchronizedCompleteP286BaseActual
          positiveSmoothUnifiedSource
          PreContorsionFullLorentzTriangularCurrent 0 by rfl,
    currentFullSynchronizedCompleteP286BaseActual_conjugateMatter_origin]
  exact congrFun
    preContorsionFullLorentzTriangularCurrent_conjugateMatter_constant 0

theorem
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_constant :
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
    fullSynchronizedActionLorentzActual
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual
    currentCanonicalFullActionBaseActual
    currentFullSynchronizedCompleteP286BaseActual
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift
  change
    actionGeneratedMatterLocalField
        PreContorsionFullLorentzTriangularCurrent 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact matterLocalField_zeroSlice_of_constant
    PreContorsionFullLorentzTriangularCurrent 0 diracSpinTwoMatterProbe
    preContorsionFullLorentzTriangularCurrent_matter_constant space

theorem
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_conjugateMatter_constant :
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState.conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
    fullSynchronizedActionLorentzActual
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual
    currentCanonicalFullActionBaseActual
    currentFullSynchronizedCompleteP286BaseActual
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift
  change
    actionGeneratedConjugateMatterLocalField
        PreContorsionFullLorentzTriangularCurrent 0
        (canonicalCauchySlicePoint 0 space) =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact conjugateMatterLocalField_zeroSlice_of_constant
    PreContorsionFullLorentzTriangularCurrent 0
    (diracSpinZeroMatterCoordinate :
      Module.Dual ℂ DiracExteriorMatterCarrier)
    preContorsionFullLorentzTriangularCurrent_conjugateMatter_constant space

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_coframe_origin :
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual.coframe 0 =
      (1 : LorentzianCoframe) := by
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).coframe 0 =
      1
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe,
    preContorsionFullLorentzTriangularCurrent_coframe_origin]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_spin_eq_einsteinCartan :
    fullSynchronizedActionSpin positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedLorentzBaseActual =
      positiveP506MatterCurrentEinsteinCartanSpinCoordinates := by
  unfold fullSynchronizedActionSpin
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates
    sourceActionGeneratedCurrentEinsteinCartanSpinCoordinates
    sourceActionGeneratedCurrentEinsteinCartanFeedbackBaseActual
  apply actualMatterSpinActionCoordinates_eq_of_origin_fields
  · rw [
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_coframe_origin]
    exact
      positiveP506MatterCurrentCartanTrajectoryActual_coframe_origin.symm
  · rw [show
        positiveP506MatterCurrentFullSynchronizedLorentzBaseActual =
          currentFullSynchronizedCompleteP286BaseActual
            positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent 0 by rfl,
      currentFullSynchronizedCompleteP286BaseActual_matter_origin,
      congrFun preContorsionFullLorentzTriangularCurrent_matter_constant 0]
    exact positiveP506MatterCurrentCartanTrajectoryActual_matter_origin.symm
  · rw [show
        positiveP506MatterCurrentFullSynchronizedLorentzBaseActual =
          currentFullSynchronizedCompleteP286BaseActual
            positiveSmoothUnifiedSource
            PreContorsionFullLorentzTriangularCurrent 0 by rfl,
      currentFullSynchronizedCompleteP286BaseActual_conjugateMatter_origin,
      congrFun
        preContorsionFullLorentzTriangularCurrent_conjugateMatter_constant 0]
    exact
      positiveP506MatterCurrentCartanTrajectoryActual_conjugate_origin.symm

theorem
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gravityConnection_origin :
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState.gravityConnection
        0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  unfold positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedLorentzBaseActual
      ).gravityConnection (canonicalCauchySlicePoint 0 0) =
      _
  rw [contactZero]
  unfold fullSynchronizedActionLorentzActual
  change
    normalizedAffineLorentzConnectionField
        (fullSynchronizedActionLorentzOrigin positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedLorentzBaseActual)
        (holonomicGravityCurvature
          positiveP506MatterCurrentFullSynchronizedLorentzBaseActual 0)
        0 =
      _
  rw [normalizedAffineLorentzConnectionField_zero]
  unfold fullSynchronizedActionLorentzOrigin
    fullSynchronizedActionContorsion
    positiveP506MatterCurrentEinsteinCartanContorsionCoordinates
    sourceActionGeneratedCurrentEinsteinCartanContorsionCoordinates
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_spin_eq_einsteinCartan]

theorem
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_gaugeConnection_origin_zero :
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState.gaugeConnection
        0 =
      0 := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  unfold positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
    fullSynchronizedActionLorentzActual
  change
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual.gaugeConnection
        (canonicalCauchySlicePoint 0 0) =
      0
  rw [contactZero]
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).gaugeConnection 0 =
      0
  rw [congrFun
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift_retainsJointPrimitiveFields
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).2.2.2.1 0]
  change
    sourceGeneratedP286ActionLocalConnection positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0 0 =
      0
  funext direction
  rw [sourceGeneratedP286ActionLocalConnection_origin,
    preContorsionFullLorentzTriangularCurrent_gaugeConnection_origin_zero]

theorem
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_scalar_origin_vacuum :
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState.scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  unfold positiveP506MatterCurrentFullSynchronizedMatterCauchyState
    fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
    fullSynchronizedActionLorentzActual
  change
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual.scalar
        (canonicalCauchySlicePoint 0 0) =
      _
  rw [contactZero]
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).scalar 0 =
      _
  rw [congrFun
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift_retainsJointPrimitiveFields
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).2.2.2.2.2.1 0,
    sourceActionGeneratedJointLocalActualLift_initialScalar,
    congrFun preContorsionFullLorentzTriangularCurrent_scalar_vacuum 0]

theorem
    preContorsionFullLorentzTriangularCurrent_gaugeAuxiliary_origin_zero :
    PreContorsionFullLorentzTriangularCurrent.gaugeAuxiliary 0 = 0 := by
  change
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 0) =
      0
  rw [
    positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual]
  change
    (currentCanonicalFullActionLorentzCoherentDiagonalActual
      positiveSmoothUnifiedSource
      PreContorsionSpatialProfileCurrent).gaugeAuxiliary
        (canonicalCauchySlicePoint 0 0) =
      0
  rw [coherentDiagonalActual_gaugeAuxiliary_slice,
    preContorsionSpatialProfileCurrent_zeroStep]
  change
    preContorsionSpatialProfileActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 0) =
      0
  rw [show canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]]
  rw [congrFun preContorsionSpatialProfileActual_retains_p286Fields.2 0]
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveSourceTargetMatterCauchyState 0)).gaugeAuxiliary 0 =
      0
  rw [currentP286CompleteActionResponseOperator_gaugeAuxiliary_origin]
  rfl

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_gaugeAuxiliary_origin_zero :
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual.gaugeAuxiliary
        0 =
      0 := by
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).gaugeAuxiliary 0 =
      0
  rw [congrFun
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift_retainsJointPrimitiveFields
      positiveSmoothUnifiedSource PreContorsionFullLorentzTriangularCurrent
      0).2.2.2.2.1 0]
  change
    PreContorsionFullLorentzTriangularCurrent.gaugeAuxiliary 0 =
      0
  exact
    preContorsionFullLorentzTriangularCurrent_gaugeAuxiliary_origin_zero

theorem
    positiveP506MatterCurrentFullSynchronizedProducerOriginField_gaugeAuxiliary_zero :
    (currentFullSynchronizedProducerOriginField positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent 0).gaugeAuxiliary =
      0 := by
  unfold currentFullSynchronizedProducerOriginField
  rw [fullSynchronizedActionMatterOriginField_gaugeAuxiliary,
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_gaugeAuxiliary_origin_zero]

/-! ## C3h203 judged-actual origin -/

theorem positiveP506MatterCurrentFullSynchronizedLorentzBaseActual_smooth :
    positiveP506MatterCurrentFullSynchronizedLorentzBaseActual.Smooth := by
  change
    (currentFullSynchronizedCompleteP286BaseActual positiveSmoothUnifiedSource
      PreContorsionFullLorentzTriangularCurrent 0).Smooth
  exact sourceActionGeneratedLinearPlebanskiJointLocalActualLift_smooth
    positiveSmoothUnifiedSource
    PreContorsionFullLorentzTriangularCurrent 0

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_matter_origin :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.matter 0 =
      diracSpinTwoMatterProbe := by
  have matterEquality := congrArg
    (fun field : StageNineContinuumPointField => field.matter)
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_nonGravity_eq_producer
  change
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.matter =
      (currentFullSynchronizedProducerOriginField positiveSmoothUnifiedSource
        PreContorsionFullLorentzTriangularCurrent 0).matter at matterEquality
  rw [currentFullSynchronizedProducerOriginField,
    fullSynchronizedActionMatterOriginField_matter,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_matter_origin]
    at matterEquality
  exact matterEquality

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_eq_localField :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.conjugateMatter =
      actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentFullSynchronizedMatterCauchyState 0 := by
  unfold
    positiveP506MatterCurrentFullSynchronizedLorentzActual
  rw [
    currentFullSynchronizedLorentzActualFirstJetLift_conjugateMatter,
    currentCanonicalFullActionActual_conjugateMatter_eq_localField]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_origin :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActual_conjugateMatter_eq_localField,
    actionGeneratedConjugateMatterLocalField_origin,
    positiveP506MatterCurrentFullSynchronizedMatterCauchyState_conjugateMatter_origin]

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzContactReadout
