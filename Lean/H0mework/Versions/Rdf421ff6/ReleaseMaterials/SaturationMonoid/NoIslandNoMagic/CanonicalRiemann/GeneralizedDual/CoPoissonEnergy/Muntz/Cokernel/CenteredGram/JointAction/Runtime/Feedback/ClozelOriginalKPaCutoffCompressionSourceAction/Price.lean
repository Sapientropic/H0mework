import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Inverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped InnerProductSpace



open scoped InnerProductSpace

/-- A physical source cotest consumes the generated positive compression Gram. -/
theorem physical_cutoff_price_complete (radius : ℝ) (material : F.Branches) :
 (inner ℂ (actualPaField material) (physicalCutoffAction radius (actualPaField material))).re +
 ‖outsideTailAction radius (actualPaField material : BurnolL2)‖^2 = ‖actualPaField material‖^2 := by
 rw [physical_cutoff_action_positive_gram]
 exact (add_comm _ _).trans (outside_tail_gram radius (actualPaField material : BurnolL2))

theorem actual_inverse_cotest_price (radius : ℝ) (material : F.Branches) (test : BurnolL2) :
 inner ℂ test (F.firstInverseResidual radius (Native.sourceFields (actualNu material))) =
 inner ℂ test (actualNu material) - inner ℂ test
  (burnolMobiusSourceL2 (physicalCutoffAction radius (actualPaField material))) := by
 rw [actual_inverse_compression_source]
 change inner ℂ test (burnolMobiusSourceL2 (actualPaField material-physicalCutoffAction radius (actualPaField material))) = _
 rw [map_sub,inner_sub_right]
 rfl

theorem actual_inverse_cotest_full_cost (radius : ℝ) (material : F.Branches) (test : BurnolL2) :
 ‖inner ℂ test (F.firstInverseResidual radius (Native.sourceFields (actualNu material)))‖ ≤
 ‖test‖ * (‖burnolMobiusSourceL2‖ * ‖outsideTailAction radius (actualPaField material : BurnolL2)‖) :=
 (norm_inner_le_norm _ _).trans
  (mul_le_mul_of_nonneg_left (actual_inverse_residual_norm_cost radius material) (norm_nonneg test))

/-- All fields retain their source; no C_r idempotence or free source norm transfer is used. -/
theorem actual_compression_complete_consumer (radius : ℝ) (material : F.Branches) (test : BurnolL2) :
 (type_of% (physical_cutoff_action_symmetric radius)) ∧
 (type_of% (physical_cutoff_action_positive_gram radius (actualPaField material))) ∧
 (type_of% (physical_cutoff_action_contractive radius (actualPaField material))) ∧
 (type_of% (physical_tail_full_gram radius (actualPaField material))) ∧
 (type_of% (actual_inverse_compression_source radius material)) ∧
 (type_of% (actual_source_recovery_is_finite_inverse radius material)) ∧
 (type_of% (actual_inverse_cotest_price radius material test)) ∧
 (type_of% (actual_inverse_cotest_full_cost radius material test)) :=
 ⟨physical_cutoff_action_symmetric _,physical_cutoff_action_positive_gram _ _,physical_cutoff_action_contractive _ _,
  physical_tail_full_gram _ _,actual_inverse_compression_source _ _,actual_source_recovery_is_finite_inverse _ _,
  actual_inverse_cotest_price _ _ _,actual_inverse_cotest_full_cost _ _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
