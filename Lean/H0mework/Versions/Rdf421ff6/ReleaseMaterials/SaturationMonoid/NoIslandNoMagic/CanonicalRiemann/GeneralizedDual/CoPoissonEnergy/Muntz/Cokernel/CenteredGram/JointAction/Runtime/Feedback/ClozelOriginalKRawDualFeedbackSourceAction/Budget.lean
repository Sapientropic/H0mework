import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
open Complex BurnolPhysicalState OriginalKExpandedInverseSourceAction
open scoped InnerProductSpace
local instance boundComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private theorem feedback_inverse_source_bound
 (feedback : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier)
 (bounded : ‖feedback‖≤(1/2:ℝ)) (source raw : BurnolQuarterMeanZeroCarrier)
 (generated : raw=source+feedback raw) : ‖raw‖≤2*‖source‖ := by
 have effect : ‖feedback raw‖≤(1/2:ℝ)*‖raw‖ :=
  (feedback.le_opNorm raw).trans (mul_le_mul_of_nonneg_right bounded (norm_nonneg _))
 have bound : ‖raw‖≤‖source‖+‖feedback raw‖ := by
  calc
   ‖raw‖=‖source+feedback raw‖ := congrArg norm generated
   _ ≤ ‖source‖+‖feedback raw‖ := norm_add_le _ _
 linarith

/-- The original inverse's source norm follows its actual signed feedback action, before any physical projection or margin. -/
theorem actual_raw_inverse_source_bound (source : BurnolQuarterMeanZeroCarrier) :
 ‖sourcePlusAction.adjoint source‖≤2*‖source‖ ∧
 ‖sourceMinusAction.adjoint source‖≤2*‖source‖ :=
 ⟨feedback_inverse_source_bound _ source_feedback_norm.1 _ _ (source_signed_feedback source).1,
  feedback_inverse_source_bound _ source_feedback_norm.2 _ _ (source_signed_feedback source).2⟩

/-- A power of the actual signed feedback contracts only its own quarter source. -/
theorem feedback_power_source_bound
 (feedback : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier)
 (actual : ‖feedback‖≤(1/2:ℝ)) (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :
 ‖(feedback^N) source‖≤(1/2:ℝ)^N*‖source‖ := by
 cases N with
 | zero => simp only [pow_zero,one_apply_eq_self,one_mul]; exact le_refl _
 | succ n =>
  exact ((feedback^(n+1)).le_opNorm source).trans
   (mul_le_mul_of_nonneg_right ((norm_pow_le' feedback (Nat.succ_pos n)).trans
    (pow_le_pow_left₀ (norm_nonneg feedback) actual (n+1))) (norm_nonneg _))

theorem actual_raw_remainder_source_bound (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :
 ‖plusSourceRemainder N source‖≤(1/2:ℝ)^N*(2*‖source‖) ∧
 ‖minusSourceRemainder N source‖≤(1/2:ℝ)^N*(2*‖source‖) :=
 ⟨(feedback_power_source_bound _ source_feedback_norm.1 _ N).trans
   (mul_le_mul_of_nonneg_left (actual_raw_inverse_source_bound source).1 (by positivity)),
  (feedback_power_source_bound _ source_feedback_norm.2 _ N).trans
   (mul_le_mul_of_nonneg_left (actual_raw_inverse_source_bound source).2 (by positivity))⟩

/-- An independent eta observer receives the actual same-source geometric error budget. -/
theorem actual_raw_remainder_eta_fee_bound (source : BurnolQuarterMeanZeroCarrier) (N : Nat)
 (test : BurnolQuarterMeanZeroCarrier) :
 ‖inner ℂ (plusSourceRemainder N source) test‖≤((1/2:ℝ)^N*(2*‖source‖))*‖test‖ ∧
 ‖inner ℂ (minusSourceRemainder N source) test‖≤((1/2:ℝ)^N*(2*‖source‖))*‖test‖ := by
 constructor
 · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (actual_raw_remainder_source_bound source N).1 (norm_nonneg _))
 · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (actual_raw_remainder_source_bound source N).2 (norm_nonneg _))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
