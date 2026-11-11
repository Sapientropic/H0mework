import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.Cvel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalKExpandedCompleteWindowSourceAction

private theorem quarter_extension_norm (source : BurnolQuarterIntervalL2) :
    ‖burnolQuarterZeroExtension source‖=‖source‖ := by
  change ‖burnolRadiusZeroExtension (1/4:ℝ) source‖=‖source‖
  rw [←burnolRadiusZeroExtensionExplicit_is_adjoint]
  exact burnolRadiusZeroExtensionValue_norm source

theorem actual_correction_tail_weighted_source_bound (value : BurnolL2) (source : BurnolQuarterIntervalL2) (t : ℝ) (N : ℕ) :
    ‖inner ℂ (burnolRadiusRestriction ((1/4:ℝ)*Real.exp t) (actualPhysicalCorrectionTail value N))
      (actualExpandedQuarterWeight source t)‖ ≤
      ((3/2:ℝ)*((1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection value‖))*‖source‖ := by
  rw [←actual_complete_window_weighted_cotest]
  apply (norm_inner_le_norm _ _).trans
  rw [(burnolMultiplicativeDilation (-t)).norm_map,quarter_extension_norm]
  exact mul_le_mul_of_nonneg_right (actual_physical_correction_tail_bound value N) (norm_nonneg source)

theorem actual_correction_tail_integral_source_bound (value : BurnolL2) (source : BurnolQuarterIntervalL2) (h : ℝ) (N : ℕ) :
    ‖∫ t : ℝ in (0:ℝ)..h, inner ℂ (burnolRadiusRestriction ((1/4:ℝ)*Real.exp t) (actualPhysicalCorrectionTail value N))
      (actualExpandedQuarterWeight source t)‖ ≤
      (((3/2:ℝ)*((1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection value‖))*‖source‖)*|h| := by
  have sourceBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := h)
    (fun t _ => actual_correction_tail_weighted_source_bound value source t N)
  simpa only [sub_zero] using sourceBound

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
