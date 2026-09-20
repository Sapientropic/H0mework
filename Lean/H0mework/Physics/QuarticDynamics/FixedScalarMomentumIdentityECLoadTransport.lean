import H0mework.Physics.QuarticDynamics.FixedScalarMomentumCarry
import H0mework.Physics.ElectricEC.FixedGravityCurvatureTargetCoordinate
import H0mework.Physics.ElectricJoint.FixedFieldTransport
import H0mework.Physics.ElectricJoint.FixedOriginCoframeClosure

/-!
# Fixed radial/scalar-current identity-EC load transport

This module transports the origin identity-EC load of the fixed
radial-plus-scalar current to the already evaluated final-common pre-EC
contact.  It only compares action data; no load coordinate or residual is
fed into either producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGravityCurvatureTargetCoordinate
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286RadialRequiredExteriorAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineTopologicalFourFormPairing
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev Radial : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConnectionActual

private abbrev Live : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

private abbrev Existing : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

private abbrev Accepted : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual 0

private abbrev LocalPreEC : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonPreECActionActual 0

private theorem canonical_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem current_coframe_eq_live :
    Current.coframe = Live.coframe := by
  calc
    Current.coframe = Algebraic.coframe :=
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_eq_algebraic
    _ = Live.coframe :=
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe
        Source FixedInput).symm

private theorem current_matter_eq_live :
    Current.matter = Live.matter := by
  calc
    Current.matter = Algebraic.matter :=
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic
    _ = Live.matter :=
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
        Source FixedInput).symm

private theorem current_conjugateMatter_eq_live :
    Current.conjugateMatter = Live.conjugateMatter := by
  calc
    Current.conjugateMatter = Algebraic.conjugateMatter :=
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic
    _ = Live.conjugateMatter :=
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
        Source FixedInput).symm

private theorem current_gravityConnection_eq_live :
    Current.gravityConnection = Live.gravityConnection := by
  change
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravityConnection =
      Live.gravityConnection
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC

private theorem current_gaugeConnection_origin_eq_live :
    Current.gaugeConnection 0 = Live.gaugeConnection 0 := by
  funext direction
  calc
    Current.gaugeConnection 0 direction =
        Algebraic.gaugeConnection 0 direction := by
      rw [
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeConnection_normalForm]
      simp [p286RadialQuarticTemporalConnection,
        p286SpatialRadialQuarticCoefficient,
        p286SpatialRadiusSquared,
        p286SpatialMetricCovectorOperator]
    _ = Live.gaugeConnection 0 direction := by
      exact congrFun (congrFun
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
          Source FixedInput).symm 0) direction

private theorem current_gaugeCurvature_origin_eq_live :
    holonomicGaugeCurvature Current 0 =
      holonomicGaugeCurvature Live 0 := by
  calc
    holonomicGaugeCurvature Current 0 =
        holonomicGaugeCurvature Radial 0 :=
      holonomicGaugeCurvature_eq_of_connection_eq Current Radial rfl 0
    _ = holonomicGaugeCurvature Algebraic 0 := by
      funext pair
      have radial := congrFun
        (fixedP506L0U6RadialQuarticConnection_curvature_zeroSlice 0) pair
      rw [canonical_zero] at radial
      have incrementZero :
          fixedP506L0U6RadialQuarticCurvatureIncrement 0 = 0 := by
        funext coordinate
        fin_cases coordinate <;>
          simp [fixedP506L0U6RadialQuarticCurvatureIncrement,
            p286SpatialRadiusSquared,
            p286SpatialMetricCovectorOperator]
      rw [incrementZero] at radial
      simp only [holonomicP286GaugeCurvatureCoordinate,
        add_zero] at radial
      exact p286CoordinateEquiv.injective radial
    _ = holonomicGaugeCurvature Live 0 :=
      (holonomicGaugeCurvature_eq_of_connection_eq Live Algebraic
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
          Source FixedInput) 0).symm

private theorem current_gaugeAuxiliary_origin_eq_live :
    Current.gaugeAuxiliary 0 = Live.gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  have currentCoordinate := congrFun
    (fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_zeroSlice
      0) pair
  have liveCoordinate := congrFun
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
      Source FixedInput 0) pair
  rw [canonical_zero] at currentCoordinate liveCoordinate
  have radialProfile :
      fixedP506L0P286RadialEulerAuxiliaryProfile 0 = 0 := by
    simp [fixedP506L0P286RadialEulerAuxiliaryProfile,
      p286SpatialRadiusSquared, p286SpatialMetricCovectorOperator]
  rw [radialProfile] at currentCoordinate
  simp only [sub_zero] at currentCoordinate
  exact currentCoordinate.trans liveCoordinate.symm

private theorem current_scalar_origin_eq_live :
    Current.scalar 0 = Live.scalar 0 := by
  have currentValue :=
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_zeroSlice_eq_algebraic
      (0 : StageNineSpatialPoint)
  rw [canonical_zero] at currentValue
  calc
    Current.scalar 0 = Algebraic.scalar 0 := currentValue
    _ = Live.scalar 0 :=
      (congrFun
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
          Source FixedInput) 0).symm

private theorem current_scalarCovariantDerivative_origin_eq_live :
    holonomicScalarCovariantDerivative Current 0 =
      holonomicScalarCovariantDerivative Live 0 := by
  have currentDerivative :=
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalarCovariantDerivative_zeroSlice
      (0 : StageNineSpatialPoint)
  rw [canonical_zero] at currentDerivative
  calc
    holonomicScalarCovariantDerivative Current 0 =
        holonomicScalarCovariantDerivative Algebraic 0 := currentDerivative
    _ = holonomicScalarCovariantDerivative Live 0 := by
      have scalarEq : Live.scalar = Algebraic.scalar :=
        sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
          Source FixedInput
      have gaugeConnectionEq :
          Live.gaugeConnection = Algebraic.gaugeConnection :=
        sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
          Source FixedInput
      symm
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [scalarEq, gaugeConnectionEq]

private theorem current_matterCovariantDerivative_origin_eq_live :
    holonomicMatterCovariantDerivative Current 0 =
      holonomicMatterCovariantDerivative Live 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [current_matter_eq_live, current_gravityConnection_eq_live,
    current_gaugeConnection_origin_eq_live]

private theorem current_rawProjection_eq_live_raw :
    identityECNonGravityContactProjection
        (toContinuumPointField Current 0) =
      identityECNonGravityContactProjection
        (toContinuumPointField Live 0) := by
  apply StageNineContinuumPointField.ext <;>
    simp only [identityECNonGravityContactProjection,
      toContinuumPointField]
  · exact congrFun current_coframe_eq_live 0
  · exact current_gaugeCurvature_origin_eq_live
  · exact current_gaugeAuxiliary_origin_eq_live
  · exact current_scalar_origin_eq_live
  · exact current_scalarCovariantDerivative_origin_eq_live
  · exact congrFun current_matter_eq_live 0
  · exact current_matterCovariantDerivative_origin_eq_live
  · exact congrFun current_conjugateMatter_eq_live 0

private theorem accepted_rawProjection_eq_local_raw :
    identityECNonGravityContactProjection
        (toContinuumPointField Accepted 0) =
      identityECNonGravityContactProjection
        (toContinuumPointField LocalPreEC 0) := by
  apply StageNineContinuumPointField.ext <;>
    simp only [identityECNonGravityContactProjection,
      toContinuumPointField]
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_coframe_eq_preEC 0) 0
  · exact holonomicGaugeCurvature_eq_of_connection_eq
      Accepted LocalPreEC
      (fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC 0) 0
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_gaugeAuxiliary 0) 0
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_scalar_eq_preEC 0) 0
  · funext direction
    unfold holonomicScalarCovariantDerivative
    rw [fixedP506L0FinalCommonActionActual_scalar_eq_preEC,
      fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC]
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_matter_eq_preEC 0) 0
  · funext direction
    unfold holonomicMatterCovariantDerivative
    rw [fixedP506L0FinalCommonActionActual_matter_eq_preEC,
      fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_preEC,
      fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC]
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_conjugateMatter_eq_preEC 0) 0

private theorem commonLoad_eq_of_projection_eq
    (first second : StageNineContinuumPointField)
    (projected :
      identityECNonGravityContactProjection first =
        identityECNonGravityContactProjection second) :
    diracDualFormNativeCoframeGaugeEulerCovector Source first +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 first =
      diracDualFormNativeCoframeGaugeEulerCovector Source second +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 second := by
  have gaugeDensity :
      diracDualFormNativeCoframeGaugeDensity Source first =
        diracDualFormNativeCoframeGaugeDensity Source second := by
    rw [←
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        Source first,
      projected,
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection]
  have matterDensity :
      diracDualFormNativeCoframeMatterDensity Source 0 first =
        diracDualFormNativeCoframeMatterDensity Source 0 second := by
    rw [←
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        Source 0 first,
      projected,
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection]
  have coframe : first.coframe = second.coframe := by
    simpa [identityECNonGravityContactProjection] using
      congrArg (fun field : StageNineContinuumPointField => field.coframe)
        projected
  unfold diracDualFormNativeCoframeGaugeEulerCovector
    diracDualFormNativeCoframeMatterEulerCovector
  rw [gaugeDensity, matterDensity, coframe]

private theorem current_commonLoad_eq_local :
    diracDualFormNativeCoframeGaugeEulerCovector Source
          (toContinuumPointField Current 0) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (toContinuumPointField Current 0) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
          (toContinuumPointField LocalPreEC 0) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (toContinuumPointField LocalPreEC 0) := by
  calc
    _ = diracDualFormNativeCoframeGaugeEulerCovector Source
          (toContinuumPointField Live 0) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (toContinuumPointField Live 0) :=
      commonLoad_eq_of_projection_eq _ _ current_rawProjection_eq_live_raw
    _ = diracDualFormNativeCoframeGaugeEulerCovector Source
          (toContinuumPointField Existing 0) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (toContinuumPointField Existing 0) := by
      rw [fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_pointField_origin_eq_existing]
    _ = diracDualFormNativeCoframeGaugeEulerCovector Source
          (toContinuumPointField Accepted 0) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (toContinuumPointField Accepted 0) :=
      fixedP506L0CompleteJointGlobalDevelopmentActual_commonCoframeLoad_origin_eq_accepted
    _ = _ :=
      commonLoad_eq_of_projection_eq _ _ accepted_rawProjection_eq_local_raw

private theorem identityECLoad_eq_rawPointField
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeIdentityECLoad Source current =
      identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        diracDualFormNativeCoframeGaugeEulerCovector Source
            (toContinuumPointField current 0) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
            (toContinuumPointField current 0) := by
  rfl

/-- Full origin identity-EC load transport for the Hessian input current. -/
theorem current_identityECLoad_eq_localPreEC :
    diracDualFormNativeIdentityECLoad Source Current =
      diracDualFormNativeIdentityECLoad Source LocalPreEC := by
  calc
    _ = identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        (diracDualFormNativeCoframeGaugeEulerCovector Source
            (toContinuumPointField Current 0) +
          diracDualFormNativeCoframeMatterEulerCovector Source 0
            (toContinuumPointField Current 0)) := by
      rw [identityECLoad_eq_rawPointField, ← add_assoc]
    _ = identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        (diracDualFormNativeCoframeGaugeEulerCovector Source
            (toContinuumPointField LocalPreEC 0) +
          diracDualFormNativeCoframeMatterEulerCovector Source 0
            (toContinuumPointField LocalPreEC 0)) := by
      rw [current_commonLoad_eq_local]
    _ = _ := by
      rw [identityECLoad_eq_rawPointField, ← add_assoc]

/-- Exact temporal-diagonal read of the transported source/action load.
This is the single authority for downstream Hessian and gravity-tail
calculations. -/
theorem current_identityECLoad_temporalDiagonal00 :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 0 0) =
      -(665 / 216 : ℝ) := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  have intrinsic :
      identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 0 0) = -(3 : ℝ) :=
    congrFun identityDiracDualECIntrinsicConstraintObservation (0 : Fin 4)
  unfold identityDiracDualECIntrinsicIIPlusObservation at intrinsic
  rw [intrinsic]
  have stress :=
    fixedP506L0FinalCommonPreECLiveNonGravityStress_temporalDiagonal00
  unfold diracDualFormNativeECLiveNonGravityCoframeStress at stress
  simp only [add_apply] at stress
  rw [add_assoc, stress]
  norm_num

/-- The spatial-temporal `10` coordinate of the transported source/action
load vanishes.  This is the lightweight authority consumed by the current
constraint-Cauchy Cartan operator. -/
theorem current_identityECLoad_spatialTemporal10_zero :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 1 0) = 0 := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  have nonGravity :
      diracDualFormNativeCoframeGaugeEulerCovector Source
            (diracDualFormNativeECNormalContactField
              (fixedP506L0FinalCommonPreECActionActual 0))
            (coframeCoordinateDirection 1 0) +
          diracDualFormNativeCoframeMatterEulerCovector Source 0
            (diracDualFormNativeECNormalContactField
              (fixedP506L0FinalCommonPreECActionActual 0))
            (coframeCoordinateDirection 1 0) = 0 := by
    simpa only [diracDualFormNativeECLiveNonGravityCoframeStress,
      add_apply] using
      fixedP506L0FinalCommonPreECLiveNonGravityStress_spatialTemporal10
  have intrinsic :
      identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe)))
          (coframeCoordinateDirection 1 0) = 0 := by
    simp +decide [identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, coframeWedge, internalBivectorDual,
      lorentzianCoframeHodge, gravityInternalPairVarianceNormalization,
      gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
      Fin.sum_univ_six]
  linear_combination intrinsic + nonGravity

/-- The already evaluated temporal-spatial coordinate is therefore available
to the Hessian producer without recomputing its action density. -/
theorem current_identityECLoad_temporalSpatial03 :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 0 3) = -(1 / 8 : ℝ) := by
  rw [current_identityECLoad_eq_localPreEC]
  exact live_identityLoad_temporalSpatial03

/-- The spatial-temporal row is transported as the same generated load
coordinate. -/
theorem current_identityECLoad_spatialTemporal30_eq_localPreEC :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 3 0) =
      diracDualFormNativeIdentityECLoad Source LocalPreEC
        (coframeCoordinateDirection 3 0) := by
  rw [current_identityECLoad_eq_localPreEC]

/-- Exact spatial-temporal load read of the fixed Hessian input current. -/
theorem current_identityECLoad_spatialTemporal30 :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 3 0) = (1 / 8 : ℝ) := by
  rw [current_identityECLoad_spatialTemporal30_eq_localPreEC]
  exact live_identityLoad_spatialTemporal30

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport
