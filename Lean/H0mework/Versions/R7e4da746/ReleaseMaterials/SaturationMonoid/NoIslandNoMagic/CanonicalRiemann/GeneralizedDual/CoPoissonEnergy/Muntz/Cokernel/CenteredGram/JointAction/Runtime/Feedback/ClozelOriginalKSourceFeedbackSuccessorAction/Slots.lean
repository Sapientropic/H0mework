import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.StepAction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open Complex BurnolPhysicalState OriginalKRawDualFeedbackSourceAction OriginalKMaterialExpandedDualSourceAction
open OriginalKFullSourceRAction
local instance slotsComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "Z" => OriginalKCvelSourceAction.actualStockExtension

def sourceCompactRead : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 OriginalRieszSource.Constructor.zeroMean.comp burnolQuarterRestriction

def sourceRawSlots (raw : FeedbackFeet) : Prior.Branches :=
 ((Z raw.1.1,Z raw.1.2),(Z raw.2.1,Z raw.2.2))

def sourceSlotsRead (value : Prior.Branches) : FeedbackFeet :=
 ((sourceCompactRead value.1.1,sourceCompactRead value.1.2),
  (sourceCompactRead value.2.1,sourceCompactRead value.2.2))

private theorem actual_compact_read (source : BurnolQuarterMeanZeroCarrier) :
 sourceCompactRead (Z source)=source := by
 apply Subtype.ext
 change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))=(source : BurnolQuarterIntervalL2)
 rw [burnolQuarterRestriction_zeroExtension,burnolQuarterMeanZeroProjection_coe]

/-- Four named source slots retain the full raw profiles, before evenness, physical readout or prices. -/
theorem source_slots_recover_raw (raw : FeedbackFeet) :
 sourceSlotsRead (sourceRawSlots raw)=raw := by
 rcases raw with ⟨⟨finitePlus,finiteMinus⟩,⟨tailPlus,tailMinus⟩⟩
 change ((sourceCompactRead (Z finitePlus),sourceCompactRead (Z finiteMinus)),
  (sourceCompactRead (Z tailPlus),sourceCompactRead (Z tailMinus)))=_
 rw [actual_compact_read,actual_compact_read,actual_compact_read,actual_compact_read]

def sourceSlotNext (value : Prior.Branches) : Prior.Branches :=
 sourceRawSlots (sourceFeedbackNext (sourceSlotsRead value))

/-- The installed operation advances actual raw feet. N appears only in this source-generated law. -/
theorem source_slots_actual_next (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :
 sourceSlotNext (sourceRawSlots (sourceRawFeet source N))=
 sourceRawSlots (sourceRawFeet source (N+1)) := by
 unfold sourceSlotNext
 rw [source_slots_recover_raw,source_actual_next_power]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
