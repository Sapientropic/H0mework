import H0mework.Physics.ElectricEC.FixedLorentzCriticalPair
import H0mework.Physics.FixedJoint.FixedCartanRestartCurvatureSpatialRegularity
import H0mework.Physics.ActualGerms.FixedCartanRestartTemporalElectricKernel
import H0mework.Physics.GlobalDevelopment.FixedTemporalElectricKernel
import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyLiveStressSpatialRegularity

/-!
# Fixed P506/L0 live EC curvature target coordinate

For the source/action-generated complete-joint global development, this
module evaluates the electric curvature kernel entering the authoritative
Einstein--Cartan write.  It combines the two temporal connection first germs
with the zero-slice Cartan spatial jets and bracket, then proves that the
generated target coefficient is exactly `1/16`.

The target and every field used below are produced before this readout.  No
residual coordinate, support branch, correction, or zero-fiber receipt is an
input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGravityCurvatureTargetCoordinate

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginPhysicalRetention
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECLorentzCriticalPair
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginAdjointDerivativeTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginMatterDivergenceClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CartanRestartCurvatureSpatialRegularity
open StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSixSectorClosure
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECConstraintObservationReplacement
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicGaugeCurvatureTransport
open StageNineIIPlusRestriction
open StageNineFormNativeIIPlusJetKinematics
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
  Matrix.cons_val_four

/-- The identity-coframe `II+` term has no temporal--spatial `(0,3)`
component. -/
theorem identityDiracDualECIntrinsicIIPlusObservation_temporalSpatial03 :
    identityDiracDualECIntrinsicIIPlusObservation
        (coframeCoordinateDirection 0 3) = 0 := by
  unfold identityDiracDualECIntrinsicIIPlusObservation
    identityDiracDualECCurvatureObservation
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
          (coframeCoordinateDirection 0 3))
        (gravityInternalPairVarianceNormalization
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe)))) =
      0
  rw [gravityInternalPairVarianceNormalization_involutive]
  simp +decide [coframeWedge, coframeCoordinateDirection,
    physicalIIPlusCoframeTangent, coframeWedgeTangent,
    internalBivectorDual, lorentzianCoframeHodge,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Matrix.one_apply, Fin.sum_univ_six]

/-- The identity-coframe `II+` term also has no spatial--temporal `(3,0)`
constraint component. -/
theorem identityDiracDualECIntrinsicIIPlusObservation_spatialTemporal30 :
    identityDiracDualECIntrinsicIIPlusObservation
        (coframeCoordinateDirection 3 0) = 0 := by
  change
    identityDiracDualECConstraintObservation
        (gravityInternalPairVarianceNormalization
          (coframeWedge (1 : LorentzianCoframe))) 3 = 0
  simpa using
    congrFun identityDiracDualECIntrinsicConstraintObservation (3 : Fin 4)

theorem live_identityLoad_temporalSpatial03 :
    diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual 0)
        (coframeCoordinateDirection 0 3) =
      -(1 / 8 : ℝ) := by
  have live :=
    fixedP506L0FinalCommonPreECLiveNonGravityStress_temporalSpatial03
  have intrinsic :=
    identityDiracDualECIntrinsicIIPlusObservation_temporalSpatial03
  unfold diracDualFormNativeECLiveNonGravityCoframeStress at live
  unfold diracDualFormNativeIdentityECLoad
  unfold identityDiracDualECIntrinsicIIPlusObservation at intrinsic
  simp only [add_apply] at live ⊢
  rw [intrinsic]
  simpa [temporalSpatial03CoframeVariation] using live

/-- The opposite spatial--temporal load coordinate is the direct `+1/8`
read of the same fixed gauge-plus-repaired-matter action fields. -/
theorem live_identityLoad_spatialTemporal30 :
    diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual 0)
        (coframeCoordinateDirection 3 0) =
      (1 / 8 : ℝ) := by
  have live :=
    fixedP506L0FinalCommonPreECLiveNonGravityStress_spatialTemporal30
  have intrinsic :=
    identityDiracDualECIntrinsicIIPlusObservation_spatialTemporal30
  unfold diracDualFormNativeECLiveNonGravityCoframeStress at live
  unfold diracDualFormNativeIdentityECLoad
  unfold identityDiracDualECIntrinsicIIPlusObservation at intrinsic
  simp only [add_apply] at live ⊢
  rw [intrinsic]
  simpa using live

theorem live_desiredEvolutionObservation_zero_two :
    diracDualFormNativeECDesiredEvolutionObservation
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual 0) 0 2 =
      (1 / 8 : ℝ) := by
  unfold diracDualFormNativeECDesiredEvolutionObservation
    identityECSpatialCoframeCoordinatesOfCovector
  change
    -diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual 0)
        (coframeCoordinateDirection 0 3) =
      (1 / 8 : ℝ)
  rw [live_identityLoad_temporalSpatial03]
  norm_num

private theorem curvatureNormalSection_four_zero
    (observation : LorentzianCoframe →L[ℝ] ℝ) :
    identityDiracDualECCurvatureNormalSection observation 4 0 =
      observation (coframeCoordinateDirection 0 3) / 2 := by
  simp +decide [identityDiracDualECCurvatureNormalSection,
    linearPlebanskiCoframeResponseOfStress,
    linearPlebanskiTraceReverse, coframeCovectorCoordinates,
    linearPlebanskiMultiplierOfCoframeResponse,
    gravityInternalPairVarianceNormalization,
    physicalIIPlusCoframeTangent, coframeWedgeTangent,
    internalBivectorDual, lorentzianCoframeHodge,
    lorentzianTwoFormSign,
    coframeCoordinateDirection, pairFirst, pairSecond,
    Matrix.trace, Matrix.one_apply, Fin.sum_univ_four]
  ring

/-- The constraint replacement preserves the electric `E₃₀` coordinate for
every already generated current/action pair. -/
theorem identityDiracDualECConstraintReplacementCurvatureTarget_four_zero
    (current actionCurvature : PhysicalBivector) :
    identityDiracDualECConstraintReplacementCurvatureTarget
        current actionCurvature 4 0 =
      current 4 0 := by
  unfold identityDiracDualECConstraintReplacementCurvatureTarget
    identityDiracDualECCurvatureTarget
    identityDiracDualECCurvatureKernelPart
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [curvatureNormalSection_four_zero,
    curvatureNormalSection_four_zero]
  rw [identityECConstraintReplacementObservation_coordinateDirection]
  simp

/-- Exact `E₃₀` readout of the branch-free temporal evolution target. -/
theorem identityDiracDualECTotalEvolutionCurvatureTarget_four_zero
    (current : PhysicalBivector)
    (desired : IdentityECSpatialCoframeCovectorCoordinates) :
    identityDiracDualECTotalEvolutionCurvatureTarget current desired 4 0 =
      desired 0 2 / 2 + (current 4 0 + current 3 1) / 2 := by
  change
    identityDiracDualECTotalEvolutionCurvatureTarget current desired 4
        (identityECTemporalSpatialPair 0) =
      desired 0 2 / 2 + (current 4 0 + current 3 1) / 2
  rw [identityDiracDualECTotalEvolutionCurvatureTarget_temporal
    current desired 4 0]
  simp +decide [identityDiracDualECTemporalEvolutionTargetCoordinates,
    identityDiracDualECTemporalEvolutionKernelPart,
    identityDiracDualECTemporalEvolutionSectionCoordinates,
    identityDiracDualECTemporalEvolutionObservation,
    identityECTemporalCurvatureOfCoordinates,
    identityECTemporalCurvatureCoordinatesOf,
    identityECTemporalSpatialPair,
    identityECSpatialCurvaturePart, identityECTemporalCurvaturePart,
    identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual,
    lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Matrix.one_apply, Fin.sum_univ_six]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  change
    current 4 0 - (-current 3 1 + current 4 0) / 2 +
          desired 0 2 / 2 =
      desired 0 2 / 2 + (current 4 0 + current 3 1) / 2
  ring

private theorem holonomicGravityCurvature_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gravityConnection = second.gravityConnection) :
    holonomicGravityCurvature first 0 =
      holonomicGravityCurvature second 0 := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [connectionEq]

private theorem fixed_preparedCurvature_eq_cartan :
    diracDualFormNativeECCauchyCurrentCurvature
        (fixedP506L0FinalCommonPreECActionActual 0) =
      holonomicGravityCurvature (fixedP506L0CartanRestartActual 0) 0 := by
  unfold diracDualFormNativeECCauchyCurrentCurvature
  apply holonomicGravityCurvature_eq_of_connection_eq
  rw [diracDualFormNativeECNormalPreparedActual,
    restrictHolonomicConfigurationToIIPlus_gravityConnection,
    fixedP506L0FinalCommonPreECActionActual_gravityConnection_eq_recentered,
    recenteredCartanRepairedConstitutiveCurrent_gravityConnection_eq_cartan]

private theorem fixed_cartanRestart_connection_origin_eq_fixedAction :
    (fixedP506L0CartanRestartActual 0).gravityConnection 0 =
      fixedActionCartanConnection := by
  calc
    _ = sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0 0 :=
      fixedP506L0CartanRestartActual_gravityConnection_origin_eq_fixedJointCartan 0
    _ = FixedP506JointActionSuccessor.gravityConnection 0 :=
      fixedJointCartanConnection_zero_eq_jointActionSuccessor_origin
    _ = fixedActionCartanConnection := by
      rw [fixedP506JointActionSuccessor_gravityConnection]
      exact fixedP506JointActual_connection_origin_eq_fixedAction

private theorem fixed_cartanRestart_originBracket_electricKernel :
    originLorentzBracketCurvature
          ((fixedP506L0CartanRestartActual 0).gravityConnection 0) 4 0 +
        originLorentzBracketCurvature
          ((fixedP506L0CartanRestartActual 0).gravityConnection 0) 3 1 =
      0 := by
  rw [fixed_cartanRestart_connection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm]
  norm_num [originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    pairFirst, pairSecond, minkowskiInternalSign,
    Fin.sum_univ_four, Fin.sum_univ_six];
  simp +decide

private theorem fixed_current_electricKernel_four_zero_three_one :
    diracDualFormNativeECCauchyCurrentCurvature
          (fixedP506L0FinalCommonPreECActionActual 0) 4 0 +
        diracDualFormNativeECCauchyCurrentCurvature
          (fixedP506L0FinalCommonPreECActionActual 0) 3 1 =
      0 := by
  rw [fixed_preparedCurvature_eq_cartan]
  unfold holonomicGravityCurvature
  dsimp only
  have pairFirstFour : pairFirst (4 : Fin 6) = 3 := by rfl
  have pairSecondFour : pairSecond (4 : Fin 6) = 1 := by rfl
  have pairFirstZero : pairFirst (0 : Fin 6) = 0 := by rfl
  have pairSecondZero : pairSecond (0 : Fin 6) = 1 := by rfl
  have pairFirstThree : pairFirst (3 : Fin 6) = 2 := by rfl
  have pairSecondThree : pairSecond (3 : Fin 6) = 3 := by rfl
  have pairFirstOne : pairFirst (1 : Fin 6) = 0 := by rfl
  have pairSecondOne : pairSecond (1 : Fin 6) = 2 := by rfl
  rw [pairFirstFour, pairSecondFour, pairFirstZero, pairSecondZero,
    pairFirstThree, pairSecondThree, pairFirstOne, pairSecondOne]
  simp +decide only [minkowskiInternalSign, if_false, one_mul]
  change
    (gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          0 1 3 1 -
        gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          1 0 3 1 +
        ∑ middle : LorentzianIndex,
          ((fixedP506L0CartanRestartActual 0).gravityConnection 0 0 3 middle *
                (fixedP506L0CartanRestartActual 0).gravityConnection 0 1 middle 1 -
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 1 3 middle *
                (fixedP506L0CartanRestartActual 0).gravityConnection 0 0 middle 1)) +
      (gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          0 2 2 3 -
        gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          2 0 2 3 +
        ∑ middle : LorentzianIndex,
          ((fixedP506L0CartanRestartActual 0).gravityConnection 0 0 2 middle *
                (fixedP506L0CartanRestartActual 0).gravityConnection 0 2 middle 3 -
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 2 2 middle *
                (fixedP506L0CartanRestartActual 0).gravityConnection 0 0 middle 3)) = 0
  have spatialOne :=
    fixedP506L0CartanRestartActual_connection_spatialDerivative_origin_zero
      (axis := (0 : Fin 3)) 0 3 1
  have spatialTwo :=
    fixedP506L0CartanRestartActual_connection_spatialDerivative_origin_zero
      (axis := (1 : Fin 3)) 0 2 3
  change
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
        1 0 3 1 = 0 at spatialOne
  change
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
        2 0 2 3 = 0 at spatialTwo
  rw [spatialOne, spatialTwo]
  have bracketZero :
    (∑ middle : LorentzianIndex,
        ((fixedP506L0CartanRestartActual 0).gravityConnection 0 0 3 middle *
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 1 middle 1 -
            (fixedP506L0CartanRestartActual 0).gravityConnection 0 1 3 middle *
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 0 middle 1)) +
      (∑ middle : LorentzianIndex,
        ((fixedP506L0CartanRestartActual 0).gravityConnection 0 0 2 middle *
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 2 middle 3 -
            (fixedP506L0CartanRestartActual 0).gravityConnection 0 2 2 middle *
              (fixedP506L0CartanRestartActual 0).gravityConnection 0 0 middle 3)) = 0 := by
    simpa [originLorentzBracketCurvature, pairFirst, pairSecond,
      minkowskiInternalSign] using
        fixed_cartanRestart_originBracket_electricKernel
  have temporalZero :=
    fixedP506L0CartanRestartActual_temporalElectricKernel_zero
  change
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          0 1 3 1 +
        gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
          0 2 2 3 =
      0 at temporalZero
  linarith

theorem live_cauchyCurvatureTarget_four_zero :
    diracDualFormNativeECCauchyCurvatureTarget
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual 0) 4 0 =
      (1 / 16 : ℝ) := by
  unfold diracDualFormNativeECCauchyCurvatureTarget
  rw [identityDiracDualECTotalEvolutionCurvatureTarget_four_zero,
    live_desiredEvolutionObservation_zero_two,
    fixed_current_electricKernel_four_zero_three_one]
  norm_num

private theorem identityECLoad_eq_rawPointField
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource current =
      identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource (toContinuumPointField current 0) +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 (toContinuumPointField current 0) := by
  rfl

private theorem commonCoframeLoad_eq_of_nonGravityProjection_eq
    (first second : StageNineContinuumPointField)
    (projected :
      identityECNonGravityContactProjection first =
        identityECNonGravityContactProjection second) :
    diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource first +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 first =
      diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource second +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 second := by
  have gaugeDensityEquality :
      diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
          first =
        diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
          second := by
    rw [←
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        positiveSmoothUnifiedSource first,
      projected,
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection]
  have matterDensityEquality :
      diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource 0
          first =
        diracDualFormNativeCoframeMatterDensity positiveSmoothUnifiedSource 0
          second := by
    rw [←
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        positiveSmoothUnifiedSource 0 first,
      projected,
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection]
  have coframeEquality : first.coframe = second.coframe := by
    simpa [identityECNonGravityContactProjection] using
      congrArg (fun field : StageNineContinuumPointField => field.coframe)
        projected
  unfold diracDualFormNativeCoframeGaugeEulerCovector
    diracDualFormNativeCoframeMatterEulerCovector
  rw [gaugeDensityEquality, matterDensityEquality, coframeEquality]

private theorem accepted_preEC_nonGravityProjection_eq :
    identityECNonGravityContactProjection
        (toContinuumPointField (fixedP506L0FinalCommonActionActual 0) 0) =
      identityECNonGravityContactProjection
        (toContinuumPointField
          (fixedP506L0FinalCommonPreECActionActual 0) 0) := by
  apply StageNineContinuumPointField.ext <;>
    simp only [identityECNonGravityContactProjection,
      toContinuumPointField]
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_coframe_eq_preEC 0) 0
  · exact holonomicGaugeCurvature_eq_of_connection_eq
      (fixedP506L0FinalCommonActionActual 0)
      (fixedP506L0FinalCommonPreECActionActual 0)
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

private theorem globalPreEC_identityECLoad_eq_localPreEC :
    diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual =
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual 0) := by
  have globalToAccepted :
      diracDualFormNativeCoframeGaugeEulerCovector
            positiveSmoothUnifiedSource
            (toContinuumPointField
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0) =
        diracDualFormNativeCoframeGaugeEulerCovector
            positiveSmoothUnifiedSource
            (toContinuumPointField (fixedP506L0FinalCommonActionActual 0) 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField
              (fixedP506L0FinalCommonActionActual 0) 0) := by
    rw [
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_pointField_origin_eq_existing]
    exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_commonCoframeLoad_origin_eq_accepted
  have acceptedToLocal :=
    commonCoframeLoad_eq_of_nonGravityProjection_eq
      (toContinuumPointField (fixedP506L0FinalCommonActionActual 0) 0)
      (toContinuumPointField
        (fixedP506L0FinalCommonPreECActionActual 0) 0)
      accepted_preEC_nonGravityProjection_eq
  calc
    _ = identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        (diracDualFormNativeCoframeGaugeEulerCovector
            positiveSmoothUnifiedSource
            (toContinuumPointField
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0)) := by
      rw [identityECLoad_eq_rawPointField, ← add_assoc]
    _ = identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        (diracDualFormNativeCoframeGaugeEulerCovector
            positiveSmoothUnifiedSource
            (toContinuumPointField (fixedP506L0FinalCommonActionActual 0) 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField
              (fixedP506L0FinalCommonActionActual 0) 0)) := by
      rw [globalToAccepted]
    _ = identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        (diracDualFormNativeCoframeGaugeEulerCovector
            positiveSmoothUnifiedSource
            (toContinuumPointField
              (fixedP506L0FinalCommonPreECActionActual 0) 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField
              (fixedP506L0FinalCommonPreECActionActual 0) 0)) := by
      rw [acceptedToLocal]
    _ = _ := by
      rw [identityECLoad_eq_rawPointField, ← add_assoc]

private theorem globalDevelopment_gravityConnection_zeroSlice_eq_cartanOrigin
    (space : StageNineSpatialPoint) :
    fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      (fixedP506L0CartanRestartActual space).gravityConnection 0 := by
  rw [fixedP506L0CartanRestartActual_connection_origin_eq_zeroSliceAction]
  change
    diracDualFormNativeActionCartanConnectionAt
        positiveSmoothUnifiedSource
        (completeJointGlobalP286Current positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor)
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionCartanConnectionAt
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor
        (canonicalCauchySlicePoint 0 space)
  have coframeEq :
      (completeJointGlobalP286Current positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor).coframe =
      FixedP506FormNativeJointActionSolvedSuccessor.coframe := by
    change
      fixedP506L0CompleteJointGlobalDevelopmentActual.coframe =
        FixedP506FormNativeJointActionSolvedSuccessor.coframe
    exact fixedP506L0CompleteJointGlobalDevelopmentActual_coframe
  have matterEq :
      (completeJointGlobalP286Current positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).matter
          (canonicalCauchySlicePoint 0 space) =
        FixedP506FormNativeJointActionSolvedSuccessor.matter
          (canonicalCauchySlicePoint 0 space) := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).matter
          (canonicalCauchySlicePoint 0 space) =
        _
    exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor space
  have conjugateMatterEq :
      (completeJointGlobalP286Current positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).conjugateMatter
          (canonicalCauchySlicePoint 0 space) =
        FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter
          (canonicalCauchySlicePoint 0 space) := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor).conjugateMatter
          (canonicalCauchySlicePoint 0 space) =
        _
    exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor space
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource
      (completeJointGlobalP286Current positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)
      FixedP506FormNativeJointActionSolvedSuccessor
      (canonicalCauchySlicePoint 0 space)
      (congrFun coframeEq (canonicalCauchySlicePoint 0 space))
      matterEq conjugateMatterEq
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeEq, spinEq]

private theorem globalDevelopment_gravityConnection_origin_eq_cartanOrigin :
    fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection 0 =
      (fixedP506L0CartanRestartActual 0).gravityConnection 0 := by
  simpa [canonicalCauchySlicePoint_zero_zero] using
    globalDevelopment_gravityConnection_zeroSlice_eq_cartanOrigin 0

/-- Every spatial derivative of the fixed source/current-only global Cartan
connection vanishes at the common origin.  This is the global-development
counterpart of the recentered Cartan-restart regularity theorem. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero
    (axis : Fin 3)
    (formDirection internalOut internalIn : LorentzianIndex)
    (differentiable : DifferentiableAt ℝ
      (fun point =>
        fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
          point formDirection internalOut internalIn) 0) :
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        axis.succ formDirection internalOut internalIn = 0 := by
  unfold gravityConnectionDerivative
  let field : BasePoint → ℝ := fun point =>
    fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
      point formDirection internalOut internalIn
  have fieldDifferentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    simpa [field, canonicalCauchySlicePoint_zero_zero] using differentiable
  have sliceDerivative :=
    fieldDifferentiable.hasFDerivAt.comp
      (0 : StageNineSpatialPoint)
      (canonicalCauchySlicePoint_hasFDerivAt 0 0)
  have sliceConstant :
      field ∘ canonicalCauchySlicePoint 0 =
        fun _ : StageNineSpatialPoint => field 0 := by
    funext space
    unfold field
    calc
      _ = (fixedP506L0CartanRestartActual space).gravityConnection 0
            formDirection internalOut internalIn := by
        exact congrFun (congrFun (congrFun
          (globalDevelopment_gravityConnection_zeroSlice_eq_cartanOrigin
            space) formDirection) internalOut) internalIn
      _ = (fixedP506L0CartanRestartActual 0).gravityConnection 0
            formDirection internalOut internalIn := by
        exact congrFun (congrFun (congrFun
          (fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero
            space) formDirection) internalOut) internalIn
      _ = fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
            0 formDirection internalOut internalIn := by
        exact congrFun (congrFun (congrFun
          globalDevelopment_gravityConnection_origin_eq_cartanOrigin.symm
            formDirection) internalOut) internalIn
  have sliceFderivZero :
      fderiv ℝ (field ∘ canonicalCauchySlicePoint 0)
          (0 : StageNineSpatialPoint) = 0 := by
    rw [sliceConstant]
    simp
  rw [sliceDerivative.fderiv] at sliceFderivZero
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] ℝ =>
      derivative (canonicalSpatialCoordinateDirection axis))
    sliceFderivZero
  simpa [field, ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection,
    canonicalCauchySlicePoint_zero_zero] using applied

private theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero'
    (axis : Fin 3)
    (formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        axis.succ formDirection internalOut internalIn = 0 := by
  by_cases differentiable : DifferentiableAt ℝ
      (fun point =>
        fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
          point formDirection internalOut internalIn) 0
  · exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero
        axis formDirection internalOut internalIn differentiable
  · unfold gravityConnectionDerivative
    rw [fderiv_zero_of_not_differentiableAt differentiable]
    rfl

/-- The actual pre-EC global connection, not merely its generated target,
has the electric curvature coordinate `E₃₀ = 1/16` at the fixed origin. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_origin_four_zero :
    holonomicGravityCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 4 0 =
      (1 / 16 : ℝ) := by
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing]
  unfold holonomicGravityCurvature
  dsimp only
  have pairFirstFour : pairFirst (4 : Fin 6) = 3 := by rfl
  have pairSecondFour : pairSecond (4 : Fin 6) = 1 := by rfl
  have pairFirstZero : pairFirst (0 : Fin 6) = 0 := by rfl
  have pairSecondZero : pairSecond (0 : Fin 6) = 1 := by rfl
  rw [pairFirstFour, pairSecondFour, pairFirstZero, pairSecondZero]
  simp +decide only [minkowskiInternalSign, if_false, one_mul]
  change
    gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          0 1 3 1 -
        gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          1 0 3 1 +
        ∑ middle : LorentzianIndex,
          (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 0 3 middle *
              fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 1 middle 1 -
            fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 1 3 middle *
              fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 0 middle 1) =
      (1 / 16 : ℝ)
  have spatialOne :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero
      (axis := (0 : Fin 3)) 0 3 1
      fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection031_differentiableAt_origin
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        1 0 3 1 = 0 at spatialOne
  have temporalOne :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_cartanConnection131_temporalDerivative_zero
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        0 1 3 1 = 0 at temporalOne
  rw [temporalOne, spatialOne]
  simp only [zero_sub, neg_zero, zero_add]
  rw [globalDevelopment_gravityConnection_origin_eq_cartanOrigin]
  have bracketFour :
      originLorentzBracketCurvature
          ((fixedP506L0CartanRestartActual 0).gravityConnection 0) 4 0 =
        (1 / 16 : ℝ) := by
    rw [fixed_cartanRestart_connection_origin_eq_fixedAction,
      fixedActionCartanConnection_eq_positiveNormalForm]
    norm_num [originLorentzBracketCurvature,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      positiveDiracDualCartanContorsionNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_four, Fin.sum_univ_six]
    simp +decide
    norm_num
  simpa [originLorentzBracketCurvature, pairFirst, pairSecond,
    minkowskiInternalSign] using bracketFour

/-- The actual global pre-EC curvature has vanishing `(E30,E23)` electric
kernel at the common origin.  This is a readout of the generated connection,
not a curvature target supplied to a writer. -/
theorem globalPreEC_currentElectricKernel_zero :
    diracDualFormNativeECCauchyCurrentCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 4 0 +
        diracDualFormNativeECCauchyCurrentCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 3 1 =
      0 := by
  rw [show
    diracDualFormNativeECCauchyCurrentCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual =
      holonomicGravityCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 by
    rfl,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing]
  unfold holonomicGravityCurvature
  dsimp only
  have pairFirstFour : pairFirst (4 : Fin 6) = 3 := by rfl
  have pairSecondFour : pairSecond (4 : Fin 6) = 1 := by rfl
  have pairFirstZero : pairFirst (0 : Fin 6) = 0 := by rfl
  have pairSecondZero : pairSecond (0 : Fin 6) = 1 := by rfl
  have pairFirstThree : pairFirst (3 : Fin 6) = 2 := by rfl
  have pairSecondThree : pairSecond (3 : Fin 6) = 3 := by rfl
  have pairFirstOne : pairFirst (1 : Fin 6) = 0 := by rfl
  have pairSecondOne : pairSecond (1 : Fin 6) = 2 := by rfl
  rw [pairFirstFour, pairSecondFour, pairFirstZero, pairSecondZero,
    pairFirstThree, pairSecondThree, pairFirstOne, pairSecondOne]
  simp +decide only [minkowskiInternalSign, if_false, one_mul]
  change
    (gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          0 1 3 1 -
        gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          1 0 3 1 +
        ∑ middle : LorentzianIndex,
          (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 0 3 middle *
              fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 1 middle 1 -
            fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 1 3 middle *
              fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 0 middle 1)) +
      (gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          0 2 2 3 -
        gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          2 0 2 3 +
        ∑ middle : LorentzianIndex,
          (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 0 2 middle *
              fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 2 middle 3 -
            fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 2 2 middle *
              fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
                0 0 middle 3)) =
      0
  have spatialOne :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero
      (axis := (0 : Fin 3)) 0 3 1
      fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection031_differentiableAt_origin
  have spatialTwo :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero
      (axis := (1 : Fin 3)) 0 2 3
      fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection023_differentiableAt_origin
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        1 0 3 1 = 0 at spatialOne
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        2 0 2 3 = 0 at spatialTwo
  rw [spatialOne, spatialTwo]
  have bracketZero :
      (∑ middle : LorentzianIndex,
        (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 0 3 middle *
            fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 1 middle 1 -
          fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 1 3 middle *
            fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 0 middle 1)) +
      (∑ middle : LorentzianIndex,
        (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 0 2 middle *
            fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 2 middle 3 -
          fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 2 2 middle *
            fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
              0 0 middle 3)) = 0 := by
    rw [globalDevelopment_gravityConnection_origin_eq_cartanOrigin]
    simpa [originLorentzBracketCurvature, pairFirst, pairSecond,
      minkowskiInternalSign] using
        fixed_cartanRestart_originBracket_electricKernel
  have temporalZero :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_temporalElectricKernel_zero
  change
    gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 1 3 1 +
        gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 2 2 3 =
      0 at temporalZero
  linarith

private theorem identityDiracDualECCurvatureObservation_temporalSpatial03
    (rawCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureObservation rawCurvature
        (coframeCoordinateDirection 0 3) =
      rawCurvature 4 0 - rawCurvature 3 1 := by
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_six]
  ring

/-- Exact temporal--spatial `(0,3)` curvature observation of the generated
global pre-EC connection. -/
theorem globalPreEC_curvatureObservation_temporalSpatial03 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0)
        (coframeCoordinateDirection 0 3) =
      (1 / 8 : ℝ) := by
  rw [identityDiracDualECCurvatureObservation_temporalSpatial03,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_origin_four_zero]
  have kernel := globalPreEC_currentElectricKernel_zero
  change
    holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 4 0 +
        holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 3 1 =
      0 at kernel
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_origin_four_zero]
      at kernel
  norm_num at kernel ⊢
  linarith

private theorem globalPreEC_curvature_origin_zero_four_eq_bracket :
    holonomicGravityCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 0 4 =
      originLorentzBracketCurvature
        (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection 0)
        0 4 := by
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing]
  change
    holonomicGravityCurvature
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 4 =
      originLorentzBracketCurvature
        (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection 0)
        0 4
  unfold holonomicGravityCurvature originLorentzBracketCurvature
  dsimp only
  have pairFirstZero : pairFirst (0 : Fin 6) = 0 := by rfl
  have pairSecondZero : pairSecond (0 : Fin 6) = 1 := by rfl
  have pairFirstFour : pairFirst (4 : Fin 6) = 3 := by rfl
  have pairSecondFour : pairSecond (4 : Fin 6) = 1 := by rfl
  rw [pairFirstZero, pairSecondZero, pairFirstFour, pairSecondFour]
  have spatialThree :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero'
      (2 : Fin 3) 1 0 1
  have spatialOne :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero'
      (0 : Fin 3) 3 0 1
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 3 1 0 1 = 0
      at spatialThree
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 1 3 0 1 = 0
      at spatialOne
  rw [spatialThree, spatialOne]
  ring

private theorem globalPreEC_curvature_origin_one_three_eq_bracket :
    holonomicGravityCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 1 3 =
      originLorentzBracketCurvature
        (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection 0)
        1 3 := by
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing]
  change
    holonomicGravityCurvature
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 1 3 =
      originLorentzBracketCurvature
        (fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection 0)
        1 3
  unfold holonomicGravityCurvature originLorentzBracketCurvature
  dsimp only
  have pairFirstOne : pairFirst (1 : Fin 6) = 0 := by rfl
  have pairSecondOne : pairSecond (1 : Fin 6) = 2 := by rfl
  have pairFirstThree : pairFirst (3 : Fin 6) = 2 := by rfl
  have pairSecondThree : pairSecond (3 : Fin 6) = 3 := by rfl
  rw [pairFirstOne, pairSecondOne, pairFirstThree, pairSecondThree]
  have spatialTwo :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero'
      (1 : Fin 3) 3 0 2
  have spatialThree :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero'
      (2 : Fin 3) 2 0 2
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 2 3 0 2 = 0
      at spatialTwo
  change
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 3 2 0 2 = 0
      at spatialThree
  rw [spatialTwo, spatialThree]
  ring

/-- Exact spatial--temporal `(3,0)` constraint-row curvature observation of
the same generated global pre-EC connection. -/
theorem globalPreEC_curvatureObservation_spatialTemporal30 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0)
        (coframeCoordinateDirection 3 0) =
      -(1 / 8 : ℝ) := by
  have row := congrFun
    (identityDiracDualECConstraintObservation_explicit
      (holonomicGravityCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0))
    (3 : Fin 4)
  change
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature
            fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0)
          (coframeCoordinateDirection 3 0) =
      -holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 0 4 +
        holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 1 3 at row
  rw [row, globalPreEC_curvature_origin_zero_four_eq_bracket,
    globalPreEC_curvature_origin_one_three_eq_bracket,
    globalDevelopment_gravityConnection_origin_eq_cartanOrigin,
    fixed_cartanRestart_connection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm]
  norm_num [originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm, loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm, pairFirst, pairSecond,
    minkowskiInternalSign, Fin.sum_univ_four, Fin.sum_univ_six]
  simp +decide
  norm_num

private theorem globalPreEC_currentElectricKernel_eq_localPreEC :
    diracDualFormNativeECCauchyCurrentCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 4 0 +
        diracDualFormNativeECCauchyCurrentCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 3 1 =
      diracDualFormNativeECCauchyCurrentCurvature
          (fixedP506L0FinalCommonPreECActionActual 0) 4 0 +
      diracDualFormNativeECCauchyCurrentCurvature
          (fixedP506L0FinalCommonPreECActionActual 0) 3 1 := by
  rw [globalPreEC_currentElectricKernel_zero,
    fixed_current_electricKernel_four_zero_three_one]

private theorem globalPreEC_desiredEvolutionObservation_zero_two :
    diracDualFormNativeECDesiredEvolutionObservation
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 2 =
      (1 / 8 : ℝ) := by
  unfold diracDualFormNativeECDesiredEvolutionObservation
    identityECSpatialCoframeCoordinatesOfCovector
  change
    -diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
        (coframeCoordinateDirection 0 3) =
      (1 / 8 : ℝ)
  rw [globalPreEC_identityECLoad_eq_localPreEC,
    live_identityLoad_temporalSpatial03]
  norm_num

private theorem globalPreEC_cauchyCurvatureTarget_four_zero :
    diracDualFormNativeECCauchyCurvatureTarget
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 4 0 =
      (1 / 16 : ℝ) := by
  unfold diracDualFormNativeECCauchyCurvatureTarget
  rw [identityDiracDualECTotalEvolutionCurvatureTarget_four_zero,
    globalPreEC_desiredEvolutionObservation_zero_two,
    globalPreEC_currentElectricKernel_zero]
  norm_num

theorem live_fullCauchyCurvatureTarget_four_zero :
    fixedP506L0CompleteJointLiveElectricECGravityCurvatureTarget 4 0 =
      (1 / 16 : ℝ) := by
  unfold fixedP506L0CompleteJointLiveElectricECGravityCurvatureTarget
    sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
    diracDualFormNativeECConstraintSurfaceCurvatureTarget
  rw [identityDiracDualECConstraintReplacementCurvatureTarget_four_zero]
  let current := fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
  let evolution := diracDualFormNativeECEvolutionWrittenCurrent
    positiveSmoothUnifiedSource current
  have curvatureEq :
      diracDualFormNativeECConstraintSurfaceCurrentCurvature evolution =
        diracDualFormNativeECCauchyCurvatureTarget
          positiveSmoothUnifiedSource current := by
    calc
      _ = holonomicGravityCurvature
            (diracDualFormNativeECCauchyConnectedActual
              positiveSmoothUnifiedSource current) 0 := by
          apply holonomicGravityCurvature_eq_of_connection_eq
          rfl
      _ = _ := diracDualFormNativeECCauchyConnection_realizes_target
        positiveSmoothUnifiedSource current
  simpa only [evolution, current] using
    (congrFun (congrFun curvatureEq 4) 0).trans
      globalPreEC_cauchyCurvatureTarget_four_zero

theorem live_einsteinCartanLorentzDelta_spatialOne_000_zero :
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta
        (canonicalCauchySlicePoint 0
          (canonicalSpatialCoordinateDirection 0)) 0 0 =
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricEinsteinCartanLorentzDelta_spatialOne_internalZero_tripleZero_eq_target_sub_one_sixteenth]
  change
    (1 / 2 : ℝ) *
        (fixedP506L0CompleteJointLiveElectricECGravityCurvatureTarget 4 0 -
          (1 / 16 : ℝ)) =
      0
  rw [live_fullCauchyCurvatureTarget_four_zero]
  norm_num


end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGravityCurvatureTargetCoordinate
