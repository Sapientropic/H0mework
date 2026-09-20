import H0mework.Physics.ActualGerms.FixedFirstGerm

/-!
# Canonical generated-actual zero-slice coframe seam

The canonical P286 action write changes the gauge connection/auxiliary pair
but retains the fixed P506/L0 coframe.  This module identifies that retained
field with the already-generated KIN-16 primitive diagonal and reads its
complete time-zero first jet.  The result supplies the actual pointwise
nondegeneracy domain needed by the whole-carrier residual calculation; it is
not a new field-local equation or a residual-derived write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualZeroSliceCoframe

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualFirstGerm
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-! ## Retained generated coframe -/

/-- The canonical P286 successor retains exactly the already-generated
KIN-16 primitive diagonal coframe. -/
theorem fixedP506L0P286CanonicalGeneratedActual_coframe_eq_primitiveDiagonal :
    fixedP506L0P286CanonicalGeneratedActual.coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe := by
  rw [canonicalGeneratedActual_coframe]
  change
    (fixedP506L0FinalCommonActionActual 0).coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
  rw [fixedP506L0FinalCommonActionActual_coframe]
  unfold recenteredCartanRepairedScalarSecondJetActual
  rw [installScalarQuadraticTimeCorrection_coframe,
    recenteredCartanRepairedConstitutiveCurrent_coframe_eq_cartan]
  unfold fixedP506L0CartanRestartActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  unfold fixedP506L0RecenteredInput
  rw [spatiallyRecenterHolonomicConfiguration_zero,
    fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]

/-! ## Complete time-zero first jet and domain -/

/-- At every spatial occurrence on the canonical time-zero slice, the one
generated successor has identity coframe and zero complete first jet. -/
theorem fixedP506L0P286CanonicalGeneratedActual_coframeFirstJet_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        fixedP506L0P286CanonicalGeneratedActual.coframe
        (canonicalCauchySlicePoint 0 space) =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [fixedP506L0P286CanonicalGeneratedActual_coframe_eq_primitiveDiagonal]
  exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space

theorem fixedP506L0P286CanonicalGeneratedActual_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalGeneratedActual.coframe
        (canonicalCauchySlicePoint 0 space) = 1 := by
  exact congrArg PointwiseLorentzianCoframeJet.coframe
    (fixedP506L0P286CanonicalGeneratedActual_coframeFirstJet_zeroSlice space)

/-- The complete time-zero slice lies in the genuine inverse-coframe domain
used by the form-native action decomposition. -/
theorem fixedP506L0P286CanonicalGeneratedActual_coframe_nondegenerate_zeroSlice
    (space : StageNineSpatialPoint) :
    Matrix.det
        (fixedP506L0P286CanonicalGeneratedActual.coframe
          (canonicalCauchySlicePoint 0 space)) ≠ 0 := by
  rw [fixedP506L0P286CanonicalGeneratedActual_coframe_zeroSlice]
  norm_num

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualZeroSliceCoframe
