import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Slots
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKRawDualFeedbackSourceAction
open OriginalKExpandedDualForcingSourceAction OriginalKMaterialExpandedDualSourceAction
local instance initComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "Z" => OriginalKCvelSourceAction.actualStockExtension

/-- Actual original field supplies the initial complete inverse tails; finite raw stock begins empty. -/
def sourceInitialSlots (t : ℝ) : Prior.Branches →L[ℂ] Prior.Branches :=
 (0 : Prior.Branches →L[ℂ] BurnolL2).prod 0 |>.prod
 (((Z).comp ((sourceDualPlusRaw t).comp originalField)).prod
  ((Z).comp ((sourceDualMinusRaw t).comp originalField)))

theorem source_initial_slots_generated (t : ℝ) (value : Prior.Branches) :
 sourceInitialSlots t value=sourceRawSlots (sourceRawFeet (sourceExpandedQuarterReader t (originalField value)) 0) := by
 change ((0,0),(Z (sourceDualPlusRaw t (originalField value)),Z (sourceDualMinusRaw t (originalField value))))=_
 simp only [sourceRawSlots,sourceRawFeet,plusSourceStock,minusSourceStock,feedbackStock,Finset.range_zero,
  Finset.sum_empty,zero_apply,plusSourceRemainder,minusSourceRemainder,pow_zero,
  ContinuousLinearMap.comp_apply,one_apply_eq_self,map_zero]
 rfl

/-- The generated initial slots keep both complete raw foot values, not only their even or physical projection. -/
theorem source_initial_raw_feet (t : ℝ) (value : Prior.Branches) :
 sourceSlotsRead (sourceInitialSlots t value)=
 sourceRawFeet (sourceExpandedQuarterReader t (originalField value)) 0 := by
 rw [source_initial_slots_generated,source_slots_recover_raw]
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
