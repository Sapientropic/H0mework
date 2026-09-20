import H0mework.Physics.RecenteredJoint.FixedCauchyEvolutionRegularity
import H0mework.Physics.RecenteredJoint.FixedFullJointGlobalConnectionNormalForm
import H0mework.Physics.IdentityHessian.CartanECNormalFixedCartanJointRegularity

/-!
# Fixed full-joint connection-origin regularity

This module identifies the KIN-12 connection origin with the zero-slice
value of the same source-generated global Cartan current.  It then compares
that value with the fixed P506/L0 Cartan contact producer.  Residual values,
support coordinates, branches, and target fields remain downstream.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointAction
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointGlobalConnectionNormalForm
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanRestart
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionProducer
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedCartanJointRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusJetKinematics
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

private abbrev CartanSectionCurrent : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual

private abbrev RecenteredSectionCurrent : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalRecenteredSectionActual

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedPrimitiveDiagonal : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual

private theorem inputActual_matter_zeroSlice_eq_primitiveDiagonal
    (space : StageNineSpatialPoint) :
    InputActual.matter (canonicalCauchySlicePoint 0 space) =
      FixedPrimitiveDiagonal.matter (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual).matter
        (canonicalCauchySlicePoint 0 space) = _
  rw [
    currentP286CompleteActionResponseOperator_matter,
    fixedGlobalMatterDualFullCauchy_matter]
  have primalZero := congrArg
    (fun state : StageNineCauchyState => state.matter space)
    (canonicalCauchyRestriction_zero_actionGeneratedCurrentCoframeMatterTimeResponseActual
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual)
  change
    fixedGlobalPrimalMatterWrittenActual.matter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.matter
        (canonicalCauchySlicePoint 0 space) at primalZero
  rw [primalZero]
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource FixedPrimitiveDiagonal).matter
        (canonicalCauchySlicePoint 0 space) = _
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter]

private theorem inputActual_conjugateMatter_zeroSlice_eq_primitiveDiagonal
    (space : StageNineSpatialPoint) :
    InputActual.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      FixedPrimitiveDiagonal.conjugateMatter
        (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual).conjugateMatter
        (canonicalCauchySlicePoint 0 space) = _
  rw [
    currentP286CompleteActionResponseOperator_conjugateMatter,
    fixedGlobalMatterDualFullCauchy_conjugateMatter]
  have adjointZero := congrArg
    (fun state : StageNineCauchyState => state.conjugateMatter space)
    (canonicalCauchyRestriction_zero_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      fixedGlobalPrimalMatterWrittenActual)
  change
    fixedGlobalMatterDualWrittenActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      fixedGlobalPrimalMatterWrittenActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) at adjointZero
  rw [adjointZero]
  have primalZero := congrArg
    (fun state : StageNineCauchyState => state.conjugateMatter space)
    (canonicalCauchyRestriction_zero_actionGeneratedCurrentCoframeMatterTimeResponseActual
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual)
  change
    fixedGlobalPrimalMatterWrittenActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) at primalZero
  rw [primalZero]
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource FixedPrimitiveDiagonal).conjugateMatter
        (canonicalCauchySlicePoint 0 space) = _
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter]

private theorem inputActual_coframeFirstJet_zeroSlice_eq_fixedJoint
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      holonomicCoframeFirstJetAt
        (sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space).coframe 0 := by
  calc
    holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalCauchySlicePoint 0 space) =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
        fixedP506JointActionSuccessor_coframe,
        fixedGlobalMatterDualP286Complete_coframe,
        fixedGlobalMatterDualFullCauchy_coframe,
        fixedGlobalFullCauchy_coframe]
      exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space
    _ = holonomicCoframeFirstJetAt
        (sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space).coframe 0 := by
      rw [sourceActionGeneratedJointLocalActualLift_coframeFirstJetAt,
        fixedCurrent_coframe_one]

private theorem primitiveDiagonal_matter_zeroSlice_eq_fixedJoint
    (space : StageNineSpatialPoint) :
    FixedPrimitiveDiagonal.matter (canonicalCauchySlicePoint 0 space) =
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space).matter 0 := by
  have diagonalZeroSlice := congrArg
    (fun state : StageNineCauchyState => state.matter space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    FixedPrimitiveDiagonal.matter (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.matter
        space at diagonalZeroSlice
  rw [diagonalZeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).matter space = _
  rw [reads.2.2.2.2.2.2.2.2.1]
  exact congrFun
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState space
      |>.2.2.2.1) 0

private theorem primitiveDiagonal_conjugateMatter_zeroSlice_eq_fixedJoint
    (space : StageNineSpatialPoint) :
    FixedPrimitiveDiagonal.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space).conjugateMatter 0 := by
  have diagonalZeroSlice := congrArg
    (fun state : StageNineCauchyState => state.conjugateMatter space)
    fixedPrimitiveDiagonal_zeroSlice
  change
    FixedPrimitiveDiagonal.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.conjugateMatter
        space at diagonalZeroSlice
  rw [diagonalZeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState space
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).conjugateMatter
        space = _
  rw [reads.2.2.2.2.2.2.2.2.2]
  exact congrFun
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual_retainsNonGravity
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState space
      |>.2.2.2.2) 0

private theorem inputActual_matter_zeroSlice_eq_fixedJoint
    (space : StageNineSpatialPoint) :
    InputActual.matter (canonicalCauchySlicePoint 0 space) =
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space).matter 0 :=
  (inputActual_matter_zeroSlice_eq_primitiveDiagonal space).trans
    (primitiveDiagonal_matter_zeroSlice_eq_fixedJoint space)

private theorem inputActual_conjugateMatter_zeroSlice_eq_fixedJoint
    (space : StageNineSpatialPoint) :
    InputActual.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space).conjugateMatter 0 :=
  (inputActual_conjugateMatter_zeroSlice_eq_primitiveDiagonal space).trans
    (primitiveDiagonal_conjugateMatter_zeroSlice_eq_fixedJoint space)

/-- The current fixed-lineage Cartan restart and the earlier fixed contact
Cartan producer consume exactly the same zero-slice coframe jet and W13
matter data.  This is an exact cross-epoch producer seam, not a transported
equation receipt. -/
theorem fixedP506L0CartanRestartActual_gravityConnection_origin_eq_fixedJointCartan
    (space : StageNineSpatialPoint) :
    (fixedP506L0CartanRestartActual space).gravityConnection 0 =
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState space 0 := by
  rw [fixedP506L0CartanRestartActual_connection_origin_eq_zeroSliceAction]
  unfold sourceActionGeneratedDiracDualCartanConnectionField
  have jetEq := inputActual_coframeFirstJet_zeroSlice_eq_fixedJoint space
  have coframeEq :
      InputActual.coframe (canonicalCauchySlicePoint 0 space) =
        (sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space).coframe 0 := by
    simpa [holonomicCoframeFirstJetAt] using
      congrArg PointwiseLorentzianCoframeJet.coframe jetEq
  have matterEq := inputActual_matter_zeroSlice_eq_fixedJoint space
  have conjugateMatterEq :=
    inputActual_conjugateMatter_zeroSlice_eq_fixedJoint space
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
      positiveSmoothUnifiedSource InputActual
      (sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState space)
      (canonicalCauchySlicePoint 0 space) 0
      coframeEq matterEq conjugateMatterEq
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [jetEq, coframeEq, spinEq]

/-- On the fixed P506/L0 lineage the action-generated Cartan restart origin
is independent of the spatial contact label. -/
theorem fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0CartanRestartActual space).gravityConnection 0 =
      (fixedP506L0CartanRestartActual 0).gravityConnection 0 := by
  calc
    _ = sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState space 0 :=
      fixedP506L0CartanRestartActual_gravityConnection_origin_eq_fixedJointCartan
        space
    _ = sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0 0 :=
      fixedJointCartanConnection_origin_eq space
    _ = _ :=
      (fixedP506L0CartanRestartActual_gravityConnection_origin_eq_fixedJointCartan
        0).symm

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  unfold canonicalSpatialContactTranslation
  exact add_zero _

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem recenteredSection_matter_zeroSlice_eq_input
    (space : StageNineSpatialPoint) :
    RecenteredSectionCurrent.matter (canonicalCauchySlicePoint 0 space) =
      InputActual.matter (canonicalCauchySlicePoint 0 space) := by
  rw [show
    RecenteredSectionCurrent.matter (canonicalCauchySlicePoint 0 space) =
      (fixedP506L0P286CanonicalRecenteredContactActual space).matter 0 by
        simp [RecenteredSectionCurrent,
          fixedP506L0P286CanonicalRecenteredSectionActual,
          spatialContactTimeAxisDiagonal,
          canonicalCauchySlicePoint_zero_zero_local]]
  change (fixedP506L0FinalCommonActionActual space).matter 0 = _
  rw [fixedP506L0FinalCommonActionActual_matter_eq_preEC,
    fixedP506L0FinalCommonPreECActionActual_matter_eq_recentered,
    recenteredCartanRepairedConstitutiveCurrent_matter_origin_eq_cartan]
  change InputActual.matter (canonicalSpatialContactTranslation space 0) = _
  rw [canonicalSpatialContactTranslation_zero_local]

private theorem recenteredSection_conjugateMatter_zeroSlice_eq_input
    (space : StageNineSpatialPoint) :
    RecenteredSectionCurrent.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      InputActual.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  rw [show
    RecenteredSectionCurrent.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      (fixedP506L0P286CanonicalRecenteredContactActual space
        ).conjugateMatter 0 by
        simp [RecenteredSectionCurrent,
          fixedP506L0P286CanonicalRecenteredSectionActual,
          spatialContactTimeAxisDiagonal,
          canonicalCauchySlicePoint_zero_zero_local]]
  change (fixedP506L0FinalCommonActionActual space).conjugateMatter 0 = _
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter_eq_preEC,
    fixedP506L0FinalCommonPreECActionActual_conjugateMatter_eq_recentered,
    recenteredCartanRepairedConstitutiveCurrent_conjugateMatter_origin_eq_cartan]
  change InputActual.conjugateMatter
      (canonicalSpatialContactTranslation space 0) = _
  rw [canonicalSpatialContactTranslation_zero_local]

private theorem recenteredSection_coframeFirstJet_zeroSlice_eq_input
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt RecenteredSectionCurrent.coframe
        (canonicalCauchySlicePoint 0 space) =
      holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506L0P286CanonicalRecenteredSectionActual_coframe_eq_primitiveDiagonal]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]

private theorem recenteredSection_spinResponse_zeroSlice_eq_input
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        RecenteredSectionCurrent (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        InputActual (canonicalCauchySlicePoint 0 space) := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
  · exact congrArg PointwiseLorentzianCoframeJet.coframe
      (recenteredSection_coframeFirstJet_zeroSlice_eq_input space)
  · exact recenteredSection_matter_zeroSlice_eq_input space
  · exact recenteredSection_conjugateMatter_zeroSlice_eq_input space

/-- The zero-slice value of the global Cartan section and the matching
source-owned fixed contact are produced from identical coframe-jet and W13
data. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gravityConnection_zeroSlice_eq_contactOrigin
    (space : StageNineSpatialPoint) :
    CartanSectionCurrent.gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      (fixedP506L0CartanRestartActual space).gravityConnection 0 := by
  rw [show
    CartanSectionCurrent.gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        RecenteredSectionCurrent (canonicalCauchySlicePoint 0 space) by
      rfl]
  rw [fixedP506L0CartanRestartActual_connection_origin_eq_zeroSliceAction]
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  have jetEq :=
    recenteredSection_coframeFirstJet_zeroSlice_eq_input space
  have coframeEq :
      RecenteredSectionCurrent.coframe (canonicalCauchySlicePoint 0 space) =
        InputActual.coframe (canonicalCauchySlicePoint 0 space) := by
    simpa [holonomicCoframeFirstJetAt] using
      congrArg PointwiseLorentzianCoframeJet.coframe jetEq
  rw [jetEq, coframeEq,
    recenteredSection_spinResponse_zeroSlice_eq_input]

/-- The final KIN-12 origin is not a separately supplied boundary datum: it
is exactly the zero-slice connection of the source-generated global Cartan
current consumed by the same full-joint action chain. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_cartanZeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        space =
      CartanSectionCurrent.gravityConnection
        (canonicalCauchySlicePoint 0 space) := by
  unfold
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointPreparedCurrent
    sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
    diracDualFormNativeECNormalPreparedActual
    diracDualFormNativeECEvolutionWrittenCurrent
  rw [restrictHolonomicConfigurationToIIPlus_gravityConnection,
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero]
  unfold diracDualFormNativeRepairedConstitutiveWrittenCurrent
  rw [diracDualFormNativeRepairedMatterWrittenCurrent_gravityConnection]
  change CartanSectionCurrent.gravityConnection
      (canonicalSpatialContactTranslation space 0) = _
  rw [canonicalSpatialContactTranslation_zero_local]

/-- The final KIN-12 origin is exactly the already generated fixed contact
Cartan origin at the same source-owned spatial occurrence. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_fixedCartanRestartOrigin
    (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        space =
      (fixedP506L0CartanRestartActual space).gravityConnection 0 := by
  exact
    (fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_cartanZeroSlice
      space).trans
      (fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gravityConnection_zeroSlice_eq_contactOrigin
        space)

/-- The exact KIN-12 origin family is spatially constant on the fixed
P506/L0 section.  This follows from same-source field identity with the
earlier Cartan contact producer, not from a residual equation. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_zero
    (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        space =
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        0 := by
  calc
    _ = (fixedP506L0CartanRestartActual space).gravityConnection 0 :=
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_fixedCartanRestartOrigin
        space
    _ = (fixedP506L0CartanRestartActual 0).gravityConnection 0 :=
      fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero space
    _ = _ :=
      (fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_fixedCartanRestartOrigin
        0).symm

/-- Every component of the exact full-joint origin profile has a genuine
spatial Fréchet derivative on the fixed P506/L0 lineage. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_component_differentiableAt
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
          candidate formDirection internalOut internalIn)
      space := by
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        candidate formDirection internalOut internalIn) =
    (fun candidate =>
      (fixedP506L0CartanRestartActual candidate).gravityConnection 0
        formDirection internalOut internalIn) by
      funext candidate
      exact congrFun (congrFun (congrFun
        (fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_fixedCartanRestartOrigin
          candidate) formDirection) internalOut) internalIn]
  exact
    fixedP506L0CartanRestartActual_gravityConnection_origin_component_differentiableAt
      space formDirection internalOut internalIn

/-- The generated global zero-slice profile and `Ω` are the same
differentiable spatial field, not merely pointwise values at one contact. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_gravityConnection_zeroSlice_component_differentiableAt
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.gravityConnection
          (canonicalCauchySlicePoint 0 candidate)
          formDirection internalOut internalIn)
      space := by
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.gravityConnection
        (canonicalCauchySlicePoint 0 candidate)
        formDirection internalOut internalIn) =
    (fun candidate =>
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        candidate formDirection internalOut internalIn) by
      funext candidate
      exact congrFun (congrFun (congrFun
        (fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_gravityConnection_zeroSlice
          candidate) formDirection) internalOut) internalIn]
  exact
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_component_differentiableAt
      space formDirection internalOut internalIn

/-- The complete lowered spatial first jet read directly from the zero slice
of the one generated global full-joint actual.  This is a derivative readout;
it does not select or construct a successor. -/
def
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  minkowskiInternalSign (pairFirst internalPair) *
    fderiv ℝ
      (fun candidate : StageNineSpatialPoint =>
        fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.gravityConnection
          (canonicalCauchySlicePoint 0 candidate)
          formDirection (pairFirst internalPair) (pairSecond internalPair))
      space (canonicalSpatialCoordinateDirection axis)

/-- The global zero-slice jet is exactly the derivative of the generated
origin family appearing in the full connection normal form. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet_eq_originFDeriv
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet
        space axis formDirection internalPair =
      minkowskiInternalSign (pairFirst internalPair) *
        fderiv ℝ
          (fun candidate : StageNineSpatialPoint =>
            fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
              candidate formDirection
              (pairFirst internalPair) (pairSecond internalPair))
          space (canonicalSpatialCoordinateDirection axis) := by
  unfold
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.gravityConnection
        (canonicalCauchySlicePoint 0 candidate)
        formDirection (pairFirst internalPair) (pairSecond internalPair)) =
    (fun candidate =>
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        candidate formDirection
        (pairFirst internalPair) (pairSecond internalPair)) by
      funext candidate
      exact congrFun (congrFun (congrFun
        (fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_gravityConnection_zeroSlice
          candidate) formDirection) (pairFirst internalPair))
        (pairSecond internalPair)]

/-- All spatial rows of the literal global zero-slice connection jet vanish:
the generated origin profile is constant on this exact source lineage. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet_eq_zero
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet
        space axis formDirection internalPair = 0 := by
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet_eq_originFDeriv]
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        candidate formDirection
        (pairFirst internalPair) (pairSecond internalPair)) =
    (fun _ =>
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin
        0 formDirection
        (pairFirst internalPair) (pairSecond internalPair)) by
      funext candidate
      exact congrFun (congrFun (congrFun
        (fixedP506L0P286CanonicalRecenteredSectionCartanFullJointConnectionOrigin_eq_zero
          candidate) formDirection) (pairFirst internalPair))
        (pairSecond internalPair)]
  simp

/-- The previously isolated whole spatial seam is now identified with a
literal read-after-write comparison on the same global actual: its zero-slice
spatial jet minus the matching contact's action-generated KIN-12 row. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointSpatialJetSeam_eq_globalZeroSlice_sub_local
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointSpatialJetSeam
        space axis formDirection internalPair =
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet
          space axis formDirection internalPair -
        fixedP506L0P286CanonicalRecenteredSectionCartanFullJointLocalLoweredFirstJet
          space axis.succ formDirection internalPair := by
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointGlobalZeroSliceLoweredSpatialFirstJet_eq_originFDeriv]
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
