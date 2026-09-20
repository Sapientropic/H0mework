import H0mework.Physics.JointVariation.ResponseOperator
import H0mework.Physics.FinalJoint.FixedGlobalRegularity
import H0mework.Physics.ScalarJets.ActionResponseOperatorFixedRegression

/-!
# Fixed P506/L0 specialization of the complete joint operator

This regression keeps the fixed proof chain out of the generic producer
module.  It identifies the source/current-only product with the already
verified fixed final-common actual, and only then reads its nine-channel
origin zero and smoothness.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionResponseOperatorFixedP506Specialization

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- On the source-owned fixed Cartan current, the generic product is exactly
the already generated final-common actual. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_fixed
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        positiveSmoothUnifiedSource (fixedP506L0CartanRestartActual space) =
      fixedP506L0FinalCommonActionActual space := by
  unfold sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
    completeJointPreECCurrent completeJointScalarSecondJetCurrent
    completeJointRepairedConstitutiveCurrent
  rw [show
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
        positiveSmoothUnifiedSource (fixedP506L0CartanRestartActual space) =
      recenteredCartanRepairedConstitutiveCurrent space by
    exact
      (recenteredCartanRepairedConstitutiveCurrent_eq_repairedCartan
        space).symm]
  rw [genericDiracDualScalarSecondJetActionResponse_fixed]
  rfl

/-- The generic source/current producer has a concrete positive nine-channel
zero-fiber specialization.  The residual is read only after the output has
been generated. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_fixed_originResidual_zero
    (space : StageNineSpatialPoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
          positiveSmoothUnifiedSource
          (fixedP506L0CartanRestartActual space)) 0 =
      0 := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_fixed]
  exact fixedP506L0FinalCommonActionResidual_zero space

theorem
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_fixed_smooth
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
      positiveSmoothUnifiedSource
      (fixedP506L0CartanRestartActual space)).Smooth := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_fixed]
  exact fixedP506L0FinalCommonActionActual_smooth space

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionResponseOperatorFixedP506Specialization
