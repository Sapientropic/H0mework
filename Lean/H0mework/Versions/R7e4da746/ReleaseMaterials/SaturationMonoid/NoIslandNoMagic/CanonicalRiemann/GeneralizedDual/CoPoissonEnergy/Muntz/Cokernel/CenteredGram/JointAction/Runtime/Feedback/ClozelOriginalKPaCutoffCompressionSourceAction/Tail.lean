import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped InnerProductSpace


/-- All outside mass stays in the original whole carrier. -/
theorem outside_tail_gram (radius : ℝ) (value : BurnolL2) :
 ‖outsideTailAction radius value‖^2 + ‖burnolRadiusRestriction radius value‖^2 = ‖value‖^2 := by
 have gram : (inner ℂ value (cutoffAction radius value)).re = ‖burnolRadiusRestriction radius value‖^2 := by
  rw [cutoff_action_inner]
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) _).symm
 change RCLike.re (inner ℂ value (cutoffAction radius value)) = _ at gram
 change ‖value-cutoffAction radius value‖^2 + _ = _
 rw [norm_sub_sq (𝕜:=ℂ),gram,show ‖cutoffAction radius value‖ = ‖burnolRadiusRestriction radius value‖ from zero_extension_norm _ _]
 ring

def projectionLeakage (radius : ℝ) (value : BurnolPaAmbientCarrier) : BurnolL2 :=
 cutoffAction radius value - (physicalCutoffAction radius value : BurnolL2)

theorem projection_leakage_gram (radius : ℝ) (value : BurnolPaAmbientCarrier) :
 ‖projectionLeakage radius value‖^2 + ‖physicalCutoffAction radius value‖^2 =
 ‖burnolRadiusRestriction radius (value : BurnolL2)‖^2 := by
 unfold projectionLeakage
 rw [norm_sub_sq (𝕜:=ℂ)]
 have projection := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  |>.inner_orthogonalProjectionOnto_eq_of_mem_right
   (physicalCutoffAction radius value) (cutoffAction radius value)
 have gram : (inner ℂ (cutoffAction radius value) (physicalCutoffAction radius value : BurnolL2)).re =
  ‖physicalCutoffAction radius value‖^2 := by
  rw [←projection]
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) _).symm
 change RCLike.re (inner ℂ (cutoffAction radius value) (physicalCutoffAction radius value : BurnolL2)) = _ at gram
 rw [gram]
 have extension := zero_extension_norm radius (burnolRadiusRestriction radius (value : BurnolL2))
 change ‖cutoffAction radius value‖ = _ at extension
 rw [extension]
 change ‖burnolRadiusRestriction radius (value : BurnolL2)‖^2 - 2 * ‖physicalCutoffAction radius value‖^2 +
  ‖physicalCutoffAction radius value‖^2 + ‖physicalCutoffAction radius value‖^2 = _
 ring

theorem physical_tail_full_gram (radius : ℝ) (value : BurnolPaAmbientCarrier) :
 ‖physicalTailAction radius value‖^2 + ‖projectionLeakage radius value‖^2 =
 ‖outsideTailAction radius (value : BurnolL2)‖^2 := by
 have cutoff := outside_tail_gram radius (value : BurnolL2)
 have leakage := projection_leakage_gram radius value
 have gram := physical_cutoff_action_positive_gram radius value
 change RCLike.re (inner ℂ value (physicalCutoffAction radius value)) = _ at gram
 change ‖outsideTailAction radius (value : BurnolL2)‖^2 + ‖burnolRadiusRestriction radius (value : BurnolL2)‖^2 = ‖value‖^2 at cutoff
 change ‖value-physicalCutoffAction radius value‖^2 + _ = _
 rw [norm_sub_sq (𝕜:=ℂ),gram]
 nlinarith

theorem physical_tail_norm_le_outside (radius : ℝ) (value : BurnolPaAmbientCarrier) :
 ‖physicalTailAction radius value‖ ≤ ‖outsideTailAction radius (value : BurnolL2)‖ := by
 have complete := physical_tail_full_gram radius value
 nlinarith [norm_nonneg (physicalTailAction radius value),norm_nonneg (outsideTailAction radius (value : BurnolL2)),
  sq_nonneg ‖projectionLeakage radius value‖]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
