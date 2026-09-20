import H0mework.Physics.CartanAction.CartanGravityAuxiliaryObstructionRegression
import H0mework.Physics.ConstrainedCauchy.ConnectionJetReadout
import H0mework.Physics.FixedJoint.FixedOriginPhysicalClosure
import H0mework.Physics.GravityResponse.AwayCurvatureNoGo

/-!
# Fixed P506/L0 joint-action six-sector closure

This module completes the six nonzero physical-sector readout on the same
source-native joint successor whose complete origin residual is already zero.
The gravity witness is obtained from the actual normalized-affine connection
field itself: a nonzero origin target is witnessed at the origin, while a
zero target still has a nonzero canonical away-point curvature coordinate
because the source-generated Cartan origin is noncommuting.

This is one same-actual acceptance readout.  It introduces neither a new
P286 gate nor a Hodge-convention epoch.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSixSectorClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCClassicalWorldAcceptance
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506JointActionOriginPhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalJointLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGravityAlgebraicKeepResponseAwayCurvatureNoGo
open StageNineHolonomicField
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineTopologicalLorentzThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

def fixedP506JointGravityAwayPoint : BasePoint :=
  coordinateDirection 0

private theorem fixedAction_zeroTarget_curvature_away_ne_zero :
    holonomicGravityCurvature
        (normalizedAffineConfiguration fixedActionCartanConnection 0)
        fixedP506JointGravityAwayPoint ≠
      0 := by
  intro curvatureZero
  have coordinateZero := congrFun (congrFun curvatureZero (0 : Fin 6)) (1 : Fin 6)
  rw [holonomicGravityCurvature_normalizedAffineConfiguration_at] at coordinateZero
  rw [fixedActionCartanConnection_eq_positiveNormalForm] at coordinateZero
  norm_num [fixedP506JointGravityAwayPoint,
    originLorentzBracketCurvature,
    normalizedAffineLorentzConnectionField,
    normalizedAffineBivectorOneForm,
    normalizedAffineBivectorComponentLinear,
    normalizedDerivativeBivector,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    coordinateDirection, baseCoordinate,
    pairFirst, pairSecond, minkowskiInternalSign,
    Fin.sum_univ_four, Fin.sum_univ_six] at coordinateZero
  simp +decide at coordinateZero

private theorem positiveSourceTargetMatterActual_coframe_one_here
    (point : BasePoint) :
    positiveSourceTargetMatterActual.coframe point = 1 := by
  rw [positiveSourceTargetMatterActual,
    sourceActionGeneratedJointLocalActualLift_coframe_at]
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

private theorem fixedCartanReactionContact_zero_actionConnection_eq_fixedAction :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedCartanReactionContact 0) 0 =
      fixedActionCartanConnection := by
  have coframeFieldEq :
      (fixedCartanReactionContact 0).coframe =
        positiveSourceTargetMatterActual.coframe := by
    funext point
    rw [fixedCartanReactionContact_coframe_one]
    exact (positiveSourceTargetMatterActual_coframe_one_here point).symm
  have coframeEq :
      (fixedCartanReactionContact 0).coframe 0 =
        positiveSourceTargetMatterActual.coframe 0 :=
    congrFun coframeFieldEq 0
  have matterEq :
      (fixedCartanReactionContact 0).matter 0 =
        positiveSourceTargetMatterActual.matter 0 := by
    calc
      _ = diracSpinTwoMatterProbe :=
        fixedCartanReactionContact_matter_origin 0
      _ = positiveSourceTargetMatterCauchyState.matter 0 :=
        positiveSourceTargetMatterCauchyState_matter.symm
      _ = _ :=
        (sourceActionGeneratedJointLocalActualLift_initialMatter
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
          0).symm
  have conjugateEq :
      (fixedCartanReactionContact 0).conjugateMatter 0 =
        positiveSourceTargetMatterActual.conjugateMatter 0 := by
    calc
      _ = diracSpinZeroMatterCoordinate :=
        fixedCartanReactionContact_conjugateMatter_origin 0
      _ = positiveSourceTargetMatterCauchyState.conjugateMatter 0 :=
        positiveSourceTargetMatterCauchyState_conjugate.symm
      _ = _ :=
        (sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
          0).symm
  have response :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource
      (fixedCartanReactionContact 0) positiveSourceTargetMatterActual 0
      coframeEq matterEq conjugateEq
  unfold fixedActionCartanConnection
    diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeFieldEq, response]

private theorem fixedCartanReactionContact_zero_coframe_eq_one :
    (fixedCartanReactionContact 0).coframe = fun _ => 1 := by
  funext point
  exact fixedCartanReactionContact_coframe_one 0 point

private theorem fixedCartanReactionContact_zero_connection_actionNative :
    (fixedCartanReactionContact 0).gravityConnection =
      fun point =>
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource (fixedCartanReactionContact 0) point := by
  funext point
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection_selfGenerated
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0 point

private theorem fixedCartanReactionContact_zero_connection_eq_fixedAction :
    (fixedCartanReactionContact 0).gravityConnection 0 =
      fixedActionCartanConnection := by
  calc
    _ =
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource (fixedCartanReactionContact 0) 0 :=
      congrFun fixedCartanReactionContact_zero_connection_actionNative 0
    _ = _ :=
      fixedCartanReactionContact_zero_actionConnection_eq_fixedAction

private theorem
    fixedIdentityECHessianCartanECNormalContactActual_zero_connection_eq_fixedAction :
    (fixedIdentityECHessianCartanECNormalContactActual 0).gravityConnection 0 =
      fixedActionCartanConnection := by
  unfold fixedIdentityECHessianCartanECNormalContactActual
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift
    diracDualFormNativeIdentityECHessianCartanCurrent
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  rw [
    sourceActionGeneratedDiracDualECNormalLocalActualLift_connection_zero,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connection_origin
      positiveSmoothUnifiedSource (fixedCartanReactionContact 0)
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        positiveSmoothUnifiedSource (fixedCartanReactionContact 0))
      fixedCartanReactionContact_zero_coframe_eq_one
      fixedCartanReactionContact_zero_connection_actionNative,
    identityECHolonomicCoframeHessianIncrementLocalActualLift_connection_origin,
    fixedCartanReactionContact_zero_connection_eq_fixedAction]

private theorem fixedP506JointCanonicalSlice_origin :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem fixedPrimitiveDiagonal_connection_origin_eq_fixedAction :
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
        0 =
      fixedActionCartanConnection := by
  have zeroSlice :=
    congrArg (fun state : StageNineCauchyState => state.gravityConnection 0)
      fixedPrimitiveDiagonal_zeroSlice
  change
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
        (canonicalCauchySlicePoint 0 0) =
      positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent.gravityConnection
        0 at zeroSlice
  rw [fixedP506JointCanonicalSlice_origin] at zeroSlice
  rw [zeroSlice]
  have reads :=
    sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent_readsContactActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState 0
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).gravityConnection
        0 =
      fixedActionCartanConnection
  rw [reads.2.1]
  rw [← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
  exact
    fixedIdentityECHessianCartanECNormalContactActual_zero_connection_eq_fixedAction

private theorem fixedP506JointFullCauchyConnectionOrigin_eq_fixedAction :
    sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
        positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual =
      fixedActionCartanConnection := by
  have normalizedAtOrigin :=
    congrFun
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_eq_normalizedAffine
        positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual)
      0
  rw [normalizedAffineLorentzConnectionField_zero] at normalizedAtOrigin
  calc
    _ =
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          positiveSmoothUnifiedSource
          fixedGlobalMatterDualWrittenActual).gravityConnection 0 :=
      normalizedAtOrigin.symm
    _ = fixedGlobalMatterDualWrittenActual.gravityConnection 0 :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
        positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual
    _ = fixedGlobalPrimalMatterWrittenActual.gravityConnection 0 :=
      congrFun
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gravityConnection
          fixedGlobalPrimalMatterWrittenActual) 0
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.gravityConnection
          0 :=
      congrFun
        (actionGeneratedCurrentCoframeMatterTimeResponseActual_gravityConnection
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual)
        0
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.gravityConnection
          0 :=
      fixedGlobalFullCauchy_connection_origin
    _ = _ := fixedPrimitiveDiagonal_connection_origin_eq_fixedAction

private theorem fixedP506JointActionSuccessor_connection_eq_normalizedAffine :
    FixedP506JointActionSuccessor.gravityConnection =
      normalizedAffineLorentzConnectionField
        (sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
          positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual)
        (sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
          positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual) := by
  calc
    _ = FixedP506JointActual.gravityConnection :=
      fixedP506JointActionSuccessor_gravityConnection
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.gravityConnection :=
      currentP286CompleteActionResponseOperator_gravityConnection
        positiveSmoothUnifiedSource
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
    _ = _ :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_eq_normalizedAffine
        positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual

private theorem fixedAction_normalizedAffine_curvature_nonzero
    (target : PhysicalBivector) :
    ∃ point,
      holonomicGravityCurvature
          (normalizedAffineConfiguration fixedActionCartanConnection target)
          point ≠
        0 := by
  by_cases targetZero : target = 0
  · subst target
    exact
      ⟨fixedP506JointGravityAwayPoint,
        fixedAction_zeroTarget_curvature_away_ne_zero⟩
  · refine ⟨0, ?_⟩
    rw [holonomicGravityCurvature_normalizedAffineConfiguration_zero]
    exact targetZero

/-- Any normalized-affine gravity write that preserves the already generated
fixed P506/L0 Cartan origin retains a nonzero gravity curvature witness,
independently of the newly generated curvature target. -/
theorem
    fixedP506JointActionSuccessorOrigin_normalizedAffine_curvature_nonzero
    (target : PhysicalBivector) :
    ∃ point,
      holonomicGravityCurvature
          (normalizedAffineConfiguration
            (FixedP506JointActionSuccessor.gravityConnection 0) target)
          point ≠
        0 := by
  have originEq :
      FixedP506JointActionSuccessor.gravityConnection 0 =
        fixedActionCartanConnection := by
    rw [fixedP506JointActionSuccessor_connection_eq_normalizedAffine,
      fixedP506JointFullCauchyConnectionOrigin_eq_fixedAction,
      normalizedAffineLorentzConnectionField_zero]
  rw [originEq]
  exact fixedAction_normalizedAffine_curvature_nonzero target

/-- The current-state Cartan producer at the fixed P506/L0 contact and the
earlier joint-action successor carry exactly the same generated connection
origin.  This is a producer-provenance seam used when a later EC write keeps
that origin while generating a new curvature target. -/
theorem fixedJointCartanConnection_zero_eq_jointActionSuccessor_origin :
    sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState 0 0 =
      FixedP506JointActionSuccessor.gravityConnection 0 := by
  calc
    _ = (fixedCartanReactionContact 0).gravityConnection 0 := by
      rfl
    _ = fixedActionCartanConnection :=
      fixedCartanReactionContact_zero_connection_eq_fixedAction
    _ = sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
          positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual :=
      fixedP506JointFullCauchyConnectionOrigin_eq_fixedAction.symm
    _ = FixedP506JointActionSuccessor.gravityConnection 0 := by
      rw [fixedP506JointActionSuccessor_connection_eq_normalizedAffine,
        normalizedAffineLorentzConnectionField_zero]

private theorem holonomicGravityCurvature_eq_of_gravityConnection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gravityConnection = second.gravityConnection)
    (point : BasePoint) :
    holonomicGravityCurvature first point =
      holonomicGravityCurvature second point := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [connectionEq]

/-- The gravity sector is nonzero on the same source-native joint successor.
The proof does not choose or tune the internally generated EC target: a
nonzero target is witnessed at the origin, while the forced zero-target
branch is witnessed at the canonical unit away-point. -/
theorem fixedP506JointActionSuccessor_gravityCurvatureNonzero :
    ∃ point,
      holonomicGravityCurvature FixedP506JointActionSuccessor point ≠ 0 := by
  let target :=
    sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
      positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual
  obtain ⟨point, curvatureNonzero⟩ :=
    fixedAction_normalizedAffine_curvature_nonzero target
  have connectionEq :
      FixedP506JointActionSuccessor.gravityConnection =
        (normalizedAffineConfiguration fixedActionCartanConnection target
          ).gravityConnection := by
    change
      FixedP506JointActionSuccessor.gravityConnection =
        normalizedAffineLorentzConnectionField fixedActionCartanConnection
          target
    rw [fixedP506JointActionSuccessor_connection_eq_normalizedAffine,
      fixedP506JointFullCauchyConnectionOrigin_eq_fixedAction]
  refine ⟨point, ?_⟩
  rw [holonomicGravityCurvature_eq_of_gravityConnection_eq
    FixedP506JointActionSuccessor
    (normalizedAffineConfiguration fixedActionCartanConnection target)
    connectionEq point]
  exact curvatureNonzero

/-- All six physical sectors are read from one and the same joint successor.
No old-world witness is spliced into this record. -/
theorem fixedP506JointActionSuccessor_simultaneousSixSectorNonzero :
    LegacySimultaneousSixSectorNonzero positiveSmoothUnifiedSource
      FixedP506JointActionSuccessor := by
  exact
    { scalarGeneratedVacuum :=
        fixedP506JointActionSuccessor_scalarGeneratedVacuum
      gravityCurvature :=
        fixedP506JointActionSuccessor_gravityCurvatureNonzero
      p286GaugeCurvature :=
        ⟨0, fixedP506JointActionSuccessor_gaugeCurvature_origin_ne_zero⟩
      breakingVacuum :=
        positive_sourceGeneratedVacuumBase_nonzero
      yukawaMass :=
        positiveP506L0_sourceGeneratedYukawaMass_ne_zero
      matterCurrent :=
        ⟨0, fixedP506JointActionSuccessor_matterCurrentNonzeroAt⟩
      stressOrSpin :=
        ⟨0, fixedP506JointActionSuccessor_stressOrSpinNonzeroAt⟩ }

/-- Current fixed-lineage checkpoint: the old actual remains the negative
control, while the same generated successor is on the complete
nine-coordinate origin zero fiber and retains all six nonzero physical
sectors.  This deliberately does not claim a global zero section or the final
Stage-9 credential. -/
theorem fixedP506JointActionSuccessor_zeroFiberSixSectorCheckpoint :
    fixedP506JointResidualSection 0 ≠ 0 ∧
      fixedP506JointActionSuccessorResidualSection 0 = 0 ∧
      FixedP506JointActionSuccessor ≠ FixedP506JointActual ∧
      LegacySimultaneousSixSectorNonzero positiveSmoothUnifiedSource
        FixedP506JointActionSuccessor := by
  rcases fixedP506JointActionWrite_origin_regression with
    ⟨oldNonzero, successorZero, changedActual⟩
  exact
    ⟨oldNonzero, successorZero, changedActual,
    fixedP506JointActionSuccessor_simultaneousSixSectorNonzero⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSixSectorClosure
