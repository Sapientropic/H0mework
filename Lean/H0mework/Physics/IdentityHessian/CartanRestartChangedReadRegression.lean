import H0mework.Physics.DualVariation.ECCauchyConstraintObstructionRegression
import H0mework.Physics.IdentityGerms.IdentityECCartanRestartOriginCurvature
import H0mework.Physics.IdentityGerms.CoframeHessianLoadStability

/-!
# Fixed P506/L0 Hessian-to-Cartan changed read

The KIN-13 identity-EC Hessian write is generated from the live KIN-8 action
load.  Its diagonal settlement changes the literal curvature read.  Restarting
the current-native Cartan producer on that same Hessian actual preserves its
origin curvature, so the resulting primitive connection cannot be the KIN-8
input connection.

This is the third fixed-lineage changed-read edge.  The Hessian settlement and
the restart curvature equality remain producer-soundness seams; only the final
whole-field inequality is recorded as the changed-read regression.  No phase,
cohomology, residual value, target connection, or branch certificate is an
input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanRestartChangedReadRegression

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanReactionLocalActualLiftRegression
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECCauchyConstraintObstructionRegression
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginFirstGerm
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureFirstGermCongruence
open StageNineJointActionLocalActualLift
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- The fixed source/action-generated KIN-13 Hessian actual. -/
def positiveDiracDualIdentityECHessianLocalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
    positiveSmoothUnifiedSource
    positiveDiracDualCartanReactionLocalActual

/-- The current-native Cartan/reaction restart on the same KIN-13 actual. -/
def positiveDiracDualIdentityECHessianCartanRestartLocalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource
    positiveDiracDualIdentityECHessianLocalActual

private theorem positiveDiracDualCartanReaction_coframe_eq_one :
    positiveDiracDualCartanReactionLocalActual.coframe =
      fun _ => 1 := by
  funext point
  change positiveSourceTargetMatterCauchyState.coframe 0 = 1
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

private theorem
    positiveDiracDualCartanReaction_connection_eq_actionNative :
    positiveDiracDualCartanReactionLocalActual.gravityConnection =
      fun point =>
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource
          positiveDiracDualCartanReactionLocalActual point := by
  funext point
  exact
    positiveDiracDualCartanReactionLocalActual_connection_selfGenerated point

private theorem positiveDiracDualCartanReaction_prepared_eq :
    diracDualFormNativeECNormalPreparedActual
        positiveDiracDualCartanReactionLocalActual =
      positiveDiracDualCartanReactionLocalActual := by
  unfold diracDualFormNativeECNormalPreparedActual
  exact
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      positiveDiracDualCartanReactionLocalActual).2
        positiveDiracDualCartanReactionLocalActual_simplicity

/-- The fixed KIN-8 lower-order temporal-dilation row is the existing
independent `-3` obstruction, now expressed in the KIN-13 action carrier. -/
private theorem positiveDiracDualCartanReaction_lowerOrder_zero_zero :
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
        positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionLocalActual 0 0 =
      -3 := by
  have obstruction :=
    positiveDiracDualCartanReactionECConstraintResidual_zero
  unfold positiveDiracDualCartanReactionECConstraintResidual at obstruction
  unfold diracDualFormNativeECCauchyCurrentCurvature at obstruction
  rw [positiveDiracDualCartanReaction_prepared_eq] at obstruction
  unfold sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    coframeCovectorCoordinates
  simpa [identityDiracDualECConstraintObservation,
    identityECConstraintCoordinatesOfCovector] using obstruction

/-- The KIN-13 same-actual settlement has zero diagonal Lorentz-skew row. -/
private theorem
    positiveDiracDualIdentityECHessian_settlement_zero_zero :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature
              positiveDiracDualIdentityECHessianLocalActual 0) +
          diracDualFormNativeIdentityECLoad
            positiveSmoothUnifiedSource
            positiveDiracDualIdentityECHessianLocalActual) 0 0 =
      0 := by
  have settlement :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_sameActual_settlement
      positiveSmoothUnifiedSource
      positiveDiracDualCartanReactionLocalActual
      positiveDiracDualCartanReactionLocalActual_smooth
      positiveDiracDualCartanReactionLocalActual_simplicity
  have coordinate :=
    congrFun (congrFun settlement (0 : LorentzianIndex))
      (0 : LorentzianIndex)
  simpa [positiveDiracDualIdentityECHessianLocalActual,
    identityECEtaAntisymmetricPart, identityECEtaAdjoint,
    minkowskiInternalSign] using coordinate

/-- The action-generated Hessian actual changes the literal origin-curvature
read.  This follows from the old `-3` row and the new zero diagonal
settlement, not from a supplied curvature target. -/
theorem positiveDiracDualIdentityECHessian_changes_curvatureRead :
    holonomicGravityCurvature
        positiveDiracDualIdentityECHessianLocalActual 0 ≠
      holonomicGravityCurvature
        positiveDiracDualCartanReactionLocalActual 0 := by
  intro curvatureEquality
  have outputZero :=
    positiveDiracDualIdentityECHessian_settlement_zero_zero
  have loadEquality :
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
          positiveDiracDualIdentityECHessianLocalActual =
        diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
          positiveDiracDualCartanReactionLocalActual := by
    simpa only [positiveDiracDualIdentityECHessianLocalActual] using
      sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_load_stable
        positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionLocalActual
        positiveDiracDualCartanReactionLocalActual_simplicity
  rw [curvatureEquality, loadEquality] at outputZero
  change
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
        positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionLocalActual 0 0 =
      0 at outputZero
  rw [positiveDiracDualCartanReaction_lowerOrder_zero_zero] at outputZero
  norm_num at outputZero

/-- Producer-soundness seam: the current-native restart reads the same origin
curvature as the KIN-13 primitive Hessian actual. -/
private theorem
    positiveDiracDualIdentityECHessianCartanRestart_curvature_eq_hessian :
    holonomicGravityCurvature
        positiveDiracDualIdentityECHessianCartanRestartLocalActual 0 =
      holonomicGravityCurvature
        positiveDiracDualIdentityECHessianLocalActual 0 := by
  unfold positiveDiracDualIdentityECHessianCartanRestartLocalActual
    positiveDiracDualIdentityECHessianLocalActual
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_curvature_origin
      positiveSmoothUnifiedSource
      positiveDiracDualCartanReactionLocalActual
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionLocalActual)
      positiveDiracDualCartanReaction_coframe_eq_one
      positiveDiracDualCartanReactionLocalActual_smooth
      positiveDiracDualCartanReaction_connection_eq_actionNative

/-- **Third fixed-lineage changed-read edge.**  The source/action-generated
KIN-13 coframe/auxiliary write forces the next current-native Cartan read to
differ from the KIN-8 input connection as a whole primitive field. -/
theorem
    positiveDiracDualIdentityECHessianCartanRestart_changes_connectionRead :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        positiveSmoothUnifiedSource
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
          positiveSmoothUnifiedSource
          positiveDiracDualCartanReactionLocalActual)).gravityConnection ≠
      positiveDiracDualCartanReactionLocalActual.gravityConnection := by
  change
    positiveDiracDualIdentityECHessianCartanRestartLocalActual.gravityConnection ≠
      positiveDiracDualCartanReactionLocalActual.gravityConnection
  intro connectionEquality
  have restartCurvatureEqInput :
      holonomicGravityCurvature
          positiveDiracDualIdentityECHessianCartanRestartLocalActual 0 =
        holonomicGravityCurvature
          positiveDiracDualCartanReactionLocalActual 0 := by
    apply holonomicGravityCurvature_eq_of_connection_firstGermAt
    · intro formDirection internalOut internalIn
      have atOrigin := congrFun connectionEquality (0 : BasePoint)
      exact
        congrFun
          (congrFun (congrFun atOrigin formDirection) internalOut)
          internalIn
    · intro derivativeDirection formDirection internalOut internalIn
      unfold gravityConnectionDerivative
      rw [connectionEquality]
  have hessianCurvatureEqInput :
      holonomicGravityCurvature
          positiveDiracDualIdentityECHessianLocalActual 0 =
        holonomicGravityCurvature
          positiveDiracDualCartanReactionLocalActual 0 :=
    positiveDiracDualIdentityECHessianCartanRestart_curvature_eq_hessian.symm.trans
      restartCurvatureEqInput
  exact
    positiveDiracDualIdentityECHessian_changes_curvatureRead
      hessianCurvatureEqInput

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanRestartChangedReadRegression
