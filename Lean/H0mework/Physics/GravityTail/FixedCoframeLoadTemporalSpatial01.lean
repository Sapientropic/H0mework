import H0mework.Physics.SynchronizedJoint.FixedCartanECSynchronizedGravityTailLorentzPath
import H0mework.Physics.SynchronizedJoint.FixedCoupledTemporalOriginProfileZero
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorMatterAdjointZeroSlice
import H0mework.Physics.QuarticDynamics.FixedHessianOffDiagonalRows

/-!
# Fixed P506 gravity-tail `E01` coframe load

The action-selected coupled temporal producer and the earlier radial-quartic
carry are two source-owned realizations of the same fixed P506/L0 primitive
data at the canonical origin.  This module compares precisely the point-field
coordinates read by the coframe density, transports the already evaluated
`E01` action load, and proves that the live gravity-tail load vanishes.

No residual value, support coordinate, target connection jet, correction,
branch, or closure receipt is supplied to a writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
open StageNineDiracDualFormNativeFixedP506ActionSelectedCoupledTemporalOriginProfileZero
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginMatterDivergenceClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonPhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianOffDiagonalRows
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev OldCarry : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Coupled

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- The action-selected gravity-tail input retains the exact fixed P506/L0
matter normal form on the full zero-time slice. -/
theorem fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    Base.matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  calc
    _ = Coupled.matter (canonicalCauchySlicePoint 0 space) := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
          Source Coupled 0).matter
            (canonicalCauchySlicePoint 0 space) = _
      rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter]
    _ = Carry.matter (canonicalCauchySlicePoint 0 space) :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        Source Carry space
    _ = OldCarry.matter (canonicalCauchySlicePoint 0 space) :=
      (actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry space).2.1
    _ = FixedInput.matter (canonicalCauchySlicePoint 0 space) := by
      rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic]
      exact
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
          Source FixedInput space
    _ = _ := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
        fixedP506JointActionSuccessor_matter,
        fixedP506JointActual_matter_zeroSlice_constant]

/-- The same input retains the fixed conjugate-matter normal form on the
full zero-time slice. -/
theorem
    fixedP506L0ActionSelectedGravityTailBase_conjugateMatter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    Base.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  calc
    _ = Coupled.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
          Source Coupled 0).conjugateMatter
            (canonicalCauchySlicePoint 0 space) = _
      rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter]
    _ = Carry.conjugateMatter (canonicalCauchySlicePoint 0 space) :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        Source Carry space
    _ = OldCarry.conjugateMatter (canonicalCauchySlicePoint 0 space) :=
      (actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry space).2.2
    _ = FixedInput.conjugateMatter
          (canonicalCauchySlicePoint 0 space) := by
      rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic]
      exact
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
          Source FixedInput space
    _ = _ := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
        fixedP506JointActionSuccessor_conjugateMatter,
        fixedP506JointActual_conjugateMatter_zeroSlice_constant]

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem base_gaugeConnection_eq_old :
    Base.gaugeConnection = OldCarry.gaugeConnection := by
  calc
    Base.gaugeConnection = Coupled.gaugeConnection :=
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
        Source Coupled 0
    _ = Carry.gaugeConnection := rfl
    _ = OldCarry.gaugeConnection :=
      actionSelectedCarry_gaugeConnection_eq_u6RadialQuarticCarry

private theorem base_gaugeAuxiliary_origin_eq_old :
    Base.gaugeAuxiliary 0 = OldCarry.gaugeAuxiliary 0 := by
  have retained :=
    actionSelectedCarry_gaugeAuxiliary_zeroSlice_eq_u6RadialQuarticCarry
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at retained
  calc
    Base.gaugeAuxiliary 0 = Coupled.gaugeAuxiliary 0 :=
      congrFun
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
          Source Coupled 0) 0
    _ = Carry.gaugeAuxiliary 0 := rfl
    _ = OldCarry.gaugeAuxiliary 0 := retained

private theorem base_scalar_origin_eq_old :
    Base.scalar 0 = OldCarry.scalar 0 := by
  have zeroSlice :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
      Source Carry (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at zeroSlice
  calc
    Base.scalar 0 = Coupled.scalar 0 :=
      congrFun
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar
          Source Coupled 0) 0
    _ = Carry.scalar 0 := zeroSlice
    _ = OldCarry.scalar 0 :=
      congrFun actionSelectedCarry_scalar_eq_u6RadialQuarticCarry 0

private theorem base_matter_origin_eq_old :
    Base.matter 0 = OldCarry.matter 0 := by
  have zeroSlice :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source Carry (0 : StageNineSpatialPoint)
  have retained :=
    actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at zeroSlice retained
  calc
    Base.matter 0 = Coupled.matter 0 :=
      congrFun
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter
          Source Coupled 0) 0
    _ = Carry.matter 0 := zeroSlice
    _ = OldCarry.matter 0 := retained.2.1

private theorem base_conjugateMatter_origin_eq_old :
    Base.conjugateMatter 0 = OldCarry.conjugateMatter 0 := by
  have zeroSlice :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source Carry (0 : StageNineSpatialPoint)
  have retained :=
    actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at zeroSlice retained
  calc
    Base.conjugateMatter 0 = Coupled.conjugateMatter 0 :=
      congrFun
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter
          Source Coupled 0) 0
    _ = Carry.conjugateMatter 0 := zeroSlice
    _ = OldCarry.conjugateMatter 0 := retained.2.2

private theorem base_coframe_origin_eq_old :
    Base.coframe 0 = OldCarry.coframe 0 := by
  have retained :=
    actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at retained
  calc
    Base.coframe 0 = 1 := congrFun
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one
      0
    _ = Carry.coframe 0 :=
      (congrFun actionSelectedCarry_coframe_eq_one 0).symm
    _ = OldCarry.coframe 0 := retained.1

private theorem base_scalarCovariantDerivative_origin_eq_old :
    holonomicScalarCovariantDerivative Base 0 =
      holonomicScalarCovariantDerivative OldCarry 0 := by
  have coupledCarry :=
    coupled_scalarCovariantDerivative_zeroSlice_eq_carry
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at coupledCarry
  have scalarEq : Base.scalar = Coupled.scalar :=
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar
      Source Coupled 0
  have gaugeConnectionEq :
      Base.gaugeConnection = Coupled.gaugeConnection :=
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
      Source Coupled 0
  calc
    holonomicScalarCovariantDerivative Base 0 =
        holonomicScalarCovariantDerivative Coupled 0 := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [scalarEq, gaugeConnectionEq]
    _ = holonomicScalarCovariantDerivative Carry 0 := coupledCarry
    _ = holonomicScalarCovariantDerivative OldCarry 0 := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [actionSelectedCarry_scalar_eq_u6RadialQuarticCarry,
        actionSelectedCarry_gaugeConnection_eq_u6RadialQuarticCarry]

private theorem coupled_matterCoordinateTemporalDerivative_origin_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Coupled.matter point)) 0
        canonicalLorentzianTimeDirection = 0 := by
  have generated :=
    actionSelectedCoupled_matterTemporalDerivative_zeroSlice
      (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local,
    fixedP506L0ActionSelectedCoupledTemporalProfile_matterVelocity_zero] at generated
  simpa using generated

private theorem oldCarry_matter_eq_newActual :
    OldCarry.matter =
      fixedP506L0CompleteJointGlobalDevelopmentActual.matter :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic.trans
    newActual_matter_eq_algebraic.symm

private theorem oldCarry_matterCoordinateTemporalDerivative_origin_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (OldCarry.matter point)) 0
        canonicalLorentzianTimeDirection = 0 := by
  rw [oldCarry_matter_eq_newActual]
  exact newActual_matterCoordinateTimeDerivative_origin_zero

private theorem base_matterCoordinateDerivative_origin_eq_old
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Base.matter point)) 0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (OldCarry.matter point)) 0 direction := by
  have matterEq : Base.matter = Coupled.matter :=
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter
      Source Coupled 0
  rw [matterEq]
  fin_cases direction
  · exact coupled_matterCoordinateTemporalDerivative_origin_zero.trans
      oldCarry_matterCoordinateTemporalDerivative_origin_zero.symm
  · calc
      _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (Carry.matter point)) 0
          (0 : Fin 3).succ := by
        simpa [canonicalCauchySlicePoint_zero_zero_local] using
          actionSelectedCoupled_matterSpatialDerivative_zeroSlice_eq_carry
            (0 : StageNineSpatialPoint) (0 : Fin 3)
      _ = _ :=
        actionSelectedCarry_matterCoordinates_spatialDerivative_eq_u6RadialQuarticCarry
          (0 : Fin 3)
  · calc
      _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (Carry.matter point)) 0
          (1 : Fin 3).succ := by
        simpa [canonicalCauchySlicePoint_zero_zero_local] using
          actionSelectedCoupled_matterSpatialDerivative_zeroSlice_eq_carry
            (0 : StageNineSpatialPoint) (1 : Fin 3)
      _ = _ :=
        actionSelectedCarry_matterCoordinates_spatialDerivative_eq_u6RadialQuarticCarry
          (1 : Fin 3)
  · calc
      _ = fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (Carry.matter point)) 0
          (2 : Fin 3).succ := by
        simpa [canonicalCauchySlicePoint_zero_zero_local] using
          actionSelectedCoupled_matterSpatialDerivative_zeroSlice_eq_carry
            (0 : StageNineSpatialPoint) (2 : Fin 3)
      _ = _ :=
        actionSelectedCarry_matterCoordinates_spatialDerivative_eq_u6RadialQuarticCarry
          (2 : Fin 3)

private theorem base_gravityConnection_origin_eq_old :
    Base.gravityConnection 0 = OldCarry.gravityConnection 0 := by
  calc
    Base.gravityConnection 0 = fixedActionCartanConnection :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_gravityConnection_origin_eq_fixedAction
    _ = OldCarry.gravityConnection 0 := by
      symm
      change
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual).gravityConnection 0 =
          fixedActionCartanConnection
      rw [congrFun
          fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC
          0,
        congrFun
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityConnection_eq_existing
          0,
        fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection_origin_eq_accepted,
        fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_jointAction,
        fixedP506JointActionSuccessor_gravityConnection]
      exact fixedP506JointActual_connection_origin_eq_fixedAction

private theorem base_matterCovariantDerivative_origin_eq_old :
    holonomicMatterCovariantDerivative Base 0 =
      holonomicMatterCovariantDerivative OldCarry 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [base_matterCoordinateDerivative_origin_eq_old direction,
    base_gravityConnection_origin_eq_old,
    base_gaugeConnection_eq_old,
    base_matter_origin_eq_old]

private theorem base_gaugeCurvature_origin_eq_old :
    holonomicGaugeCurvature Base 0 =
      holonomicGaugeCurvature OldCarry 0 :=
  holonomicGaugeCurvature_eq_of_connection_eq
    Base OldCarry base_gaugeConnection_eq_old 0

private theorem base_old_nonGravityProjection_eq :
    identityECNonGravityContactProjection
        (diracDualFormNativeCoframeECContactField Base 0) =
      identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField OldCarry) := by
  unfold diracDualFormNativeCoframeECContactField
    diracDualFormNativeCoframeECContactPreparedActual
    diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus,
    toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  apply StageNineContinuumPointField.ext <;>
    simp only [identityECNonGravityContactProjection,
      restrictContinuumPointFieldToIIPlus,
      toContinuumPointField]
  · exact base_coframe_origin_eq_old
  · exact base_gaugeCurvature_origin_eq_old
  · exact base_gaugeAuxiliary_origin_eq_old
  · exact base_scalar_origin_eq_old
  · exact base_scalarCovariantDerivative_origin_eq_old
  · exact base_matter_origin_eq_old
  · exact base_matterCovariantDerivative_origin_eq_old
  · exact base_conjugateMatter_origin_eq_old

private theorem commonCoframeLoad_eq_of_nonGravityProjection_eq
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

/-- The complete fixed action-selected gravity-tail contact load is the same
source/action density as the earlier radial-quartic identity-EC load.  This
is the whole-covector authority behind all downstream coordinate reads; it
transports no residual or closure certificate. -/
theorem
    fixedP506L0ActionSelectedGravityTail_contactLoad_eq_u6RadialQuarticIdentityLoad :
    diracDualFormNativeCoframeECContactLoad Source Base 0 =
      diracDualFormNativeIdentityECLoad Source OldCarry := by
  have commonLoad :=
    commonCoframeLoad_eq_of_nonGravityProjection_eq
      (diracDualFormNativeCoframeECContactField Base 0)
      (diracDualFormNativeECNormalContactField OldCarry)
      base_old_nonGravityProjection_eq
  have baseCoframe : Base.coframe 0 = 1 :=
    congrFun
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one
      0
  have intrinsic :
      coframeDiracDualECCurvatureObservation (1 : LorentzianCoframe)
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) =
        identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) := by
    rfl
  unfold diracDualFormNativeCoframeECContactLoad
    diracDualFormNativeIdentityECLoad
  rw [baseCoframe, intrinsic]
  simpa only [← add_assoc] using congrArg
    (fun load : LorentzianCoframe →L[ℝ] ℝ =>
      identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) + load)
    commonLoad

/-- The fixed action-selected gravity-tail contact has zero live `E01`
coframe load.  The proof transports the exact action density from the earlier
fixed P506/L0 carry; no load coordinate is consumed by a producer. -/
theorem fixedP506L0ActionSelectedGravityTail_coframeLoad_temporalSpatial01_zero :
    diracDualFormNativeCoframeECContactLoad Source Base 0
        (coframeCoordinateDirection 0 1) = 0 := by
  rw [fixedP506L0ActionSelectedGravityTail_contactLoad_eq_u6RadialQuarticIdentityLoad,
    current_identityECLoad_temporalSpatial01_zero]

/-- The same source/action density also has zero live `E02` coframe load at
the gravity-tail Base contact. -/
theorem fixedP506L0ActionSelectedGravityTail_coframeLoad_temporalSpatial02_zero :
    diracDualFormNativeCoframeECContactLoad Source Base 0
        (coframeCoordinateDirection 0 2) = 0 := by
  rw [fixedP506L0ActionSelectedGravityTail_contactLoad_eq_u6RadialQuarticIdentityLoad,
    current_identityECLoad_temporalSpatial02_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
