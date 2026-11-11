import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPaNativePortSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaNativePortSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativePortSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution

local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem r_code_read (c : BurnolCompletedMellinCoordinate) (environment : Env Value Var) :
    (rCode c).eval environment = burnolDirectRightResolventCLM c (environment () 0) := rfl

theorem correction_code_read (c : BurnolCompletedMellinCoordinate) (environment : Env Value Var) :
    (correctionCode c).eval environment = environment () 0 - unitAction c (environment () 1) := by
  change environment () 0 + (-unitAction c) (environment () 1) = _
  rw [neg_apply, sub_eq_add_neg]

theorem unit_action_physical (c : BurnolCompletedMellinCoordinate) (input : BurnolPaAmbientCarrier) :
    unitAction c (input : BurnolL2) =
      burnolPaResolventSourceCoefficient c input • burnolUnitTailResponse c 4 := by
  change burnolPaResolventSourceCoefficient c
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).orthogonalProjectionOnto input.val) •
    burnolUnitTailResponse c 4 = burnolPaResolventSourceCoefficient c input •
      burnolUnitTailResponse c 4
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- Qualification is consumed only after the actual two reader environments have been generated. -/
theorem actual_correction_code (c : BurnolCompletedMellinCoordinate)
    (environment : Env Value Var) (input : ↥OriginalKCrossParameterRAdjointSource.PaNativePortSource.Pa)
    (actualR : environment () 0 = burnolDirectRightResolventCLM c (input.val : BurnolL2))
    (actualPa : environment () 1 = (input.val : BurnolL2)) :
    (correctionCode c).eval environment =
      ((OriginalKCrossParameterRAdjointSource.PaNativePortSource.correction c input).val : BurnolL2) := by
  rw [correction_code_read, actualR, actualPa, unit_action_physical]
  rfl

end OriginalKPaNativePortSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
