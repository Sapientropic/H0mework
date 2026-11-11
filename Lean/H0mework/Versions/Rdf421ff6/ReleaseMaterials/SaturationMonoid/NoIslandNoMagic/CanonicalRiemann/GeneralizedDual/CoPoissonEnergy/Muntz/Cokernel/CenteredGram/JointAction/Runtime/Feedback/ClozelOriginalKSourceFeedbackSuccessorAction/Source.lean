import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open Complex BurnolPhysicalState OriginalKRawDualFeedbackSourceAction OriginalKExpandedDualForcingSourceAction
open OriginalKExpandedInverseSourceAction OriginalKMaterialExpandedDualSourceAction
local instance sourceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- One source programme keeps its literal finite raw stock and complete raw tail separately. -/
abbrev FeedbackFeet := (BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier) ×
 (BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier)

def sourceRawFeet (source : BurnolQuarterMeanZeroCarrier) (N : Nat) : FeedbackFeet :=
 ((plusSourceStock N source,minusSourceStock N source),
  (plusSourceRemainder N source,minusSourceRemainder N source))

def sourcePowerFeet (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :=
 ((plusFeedback^N) source,(minusFeedback^N) source)

/-- The source tail itself supplies the next power. Neither a target price nor a runtime counter enters. -/
def sourceTailPower (raw : FeedbackFeet) : BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier :=
 (raw.2.1-plusFeedback raw.2.1,raw.2.2-minusFeedback raw.2.2)

def sourceFeedbackNext (raw : FeedbackFeet) : FeedbackFeet :=
 ((raw.1.1+(sourceTailPower raw).1,raw.1.2+(sourceTailPower raw).2),
  (plusFeedback raw.2.1,minusFeedback raw.2.2))

private theorem actual_tail_power
 (feedback : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier)
 (source raw : BurnolQuarterMeanZeroCarrier) (generated : raw=source+feedback raw) (N : Nat) :
 (feedback^N) raw-feedback ((feedback^N) raw)=(feedback^N) source := by
 have own := congrArg (fun value => (feedback^N) value) generated
 have commute : (feedback^N) (feedback raw)=feedback ((feedback^N) raw) := by
  calc
   _ = (feedback^(N+1)) raw := by rw [pow_succ,mul_apply_eq_comp]
   _ = _ := by rw [pow_succ',mul_apply_eq_comp]
 rw [map_add,commute] at own
 exact (eq_sub_of_add_eq own.symm).symm

theorem source_actual_tail_generates_power (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :
 sourceTailPower (sourceRawFeet source N)=sourcePowerFeet source N :=
 Prod.ext
  (actual_tail_power plusFeedback source (sourcePlusAction.adjoint source)
   (source_signed_feedback source).1 N)
  (actual_tail_power minusFeedback source (sourceMinusAction.adjoint source)
   (source_signed_feedback source).2 N)

theorem source_actual_next_power (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :
 sourceFeedbackNext (sourceRawFeet source N)=sourceRawFeet source (N+1) := by
 have power := source_actual_tail_generates_power source N
 unfold sourceFeedbackNext
 rw [power]
 apply Prod.ext
 · apply Prod.ext <;> simp only [sourceRawFeet,sourcePowerFeet,plusSourceStock,minusSourceStock,
     feedbackStock,Finset.sum_range_succ,add_apply]
 · apply Prod.ext <;> simp only [sourceRawFeet,plusSourceRemainder,minusSourceRemainder,
     ContinuousLinearMap.comp_apply,pow_succ',mul_apply_eq_comp]

/-- All raw source stock is conserved by the genuine tail-driven action. -/
theorem source_feedback_whole_conserved (raw : FeedbackFeet) :
 (sourceFeedbackNext raw).1.1+(sourceFeedbackNext raw).2.1=raw.1.1+raw.2.1 ∧
 (sourceFeedbackNext raw).1.2+(sourceFeedbackNext raw).2.2=raw.1.2+raw.2.2 := by
 unfold sourceFeedbackNext sourceTailPower
 constructor <;> module
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
