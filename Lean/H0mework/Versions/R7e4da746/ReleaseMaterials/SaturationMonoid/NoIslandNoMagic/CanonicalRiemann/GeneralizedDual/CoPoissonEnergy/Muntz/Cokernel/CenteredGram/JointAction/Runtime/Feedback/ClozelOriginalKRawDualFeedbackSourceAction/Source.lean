import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedDualForcingSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
open Complex BurnolPhysicalState OriginalKExpandedInverseSourceAction OriginalKExpandedDualForcingSourceAction
open scoped InnerProductSpace
local instance sourceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier

def plusFeedback : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier := (T).adjoint

def minusFeedback : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier := -(T).adjoint

/-- The original source inverse generates each signed feedback update; this is not a residual-zero premise. -/
theorem source_signed_feedback (source : BurnolQuarterMeanZeroCarrier) :
 sourcePlusAction.adjoint source=source+plusFeedback (sourcePlusAction.adjoint source) ∧
 sourceMinusAction.adjoint source=source+minusFeedback (sourceMinusAction.adjoint source) := by
 have actual := source_dual_signed_forcing source
 have plus : sourcePlusAction.adjoint source-(T).adjoint (sourcePlusAction.adjoint source)=source := by
  simpa only [sourceDualPlusForcing,map_sub,ContinuousLinearMap.adjoint_one,sub_apply,one_apply_eq_self] using actual.1
 have minus : sourceMinusAction.adjoint source+(T).adjoint (sourceMinusAction.adjoint source)=source := by
  simpa only [sourceDualMinusForcing,map_add,ContinuousLinearMap.adjoint_one,add_apply,one_apply_eq_self] using actual.2
 constructor
 · exact eq_add_of_sub_eq plus
 · unfold minusFeedback
   rw [neg_apply,←sub_eq_add_neg]
   exact eq_sub_of_add_eq minus

theorem source_feedback_norm : ‖plusFeedback‖≤(1/2:ℝ) ∧ ‖minusFeedback‖≤(1/2:ℝ) := by
 have actual : ‖(T).adjoint‖=‖T‖ := ContinuousLinearMap.adjoint.norm_map _
 constructor
 · change ‖(T).adjoint‖≤_
   rw [actual]
   exact burnolMeanZeroTruncatedFourier_opNorm_le_half
 · change ‖-(T).adjoint‖≤_
   rw [norm_neg,actual]
   exact burnolMeanZeroTruncatedFourier_opNorm_le_half

/-- The actor first emits finite source stock; its exact remainder is a power of the same feedback acting on the original raw source. -/
def feedbackStock (feedback : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier) (N : Nat) :
 BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 ∑ k ∈ Finset.range N,feedback^k

theorem source_feedback_finite_and_remainder
 (feedback : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier)
 (source raw : BurnolQuarterMeanZeroCarrier) (generated : raw=source+feedback raw) (N : Nat) :
 raw=feedbackStock feedback N source+(feedback^N) raw := by
 induction N with
 | zero => simp only [feedbackStock,Finset.range_zero,Finset.sum_empty,zero_apply,pow_zero,one_apply_eq_self,zero_add]
 | succ N prior =>
  unfold feedbackStock at prior ⊢
  rw [Finset.sum_range_succ,add_apply,pow_succ,mul_apply_eq_comp]
  have next := congrArg (fun value => (feedback^N) value) generated
  rw [map_add] at next
  rw [add_assoc,←next]
  exact prior

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
