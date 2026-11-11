import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open scoped InnerProductSpace
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackSuccessorAction
 (sourceInitBornPacket actualNextSourceFrame sourceNextFrame sourceActualContinuation actualNestedSourceBinding
  sourceNextBase source_init_born_grade sourceActualCode sourceActualEnvironment sourceFeedbackNext sourceSlotsRead sourceRawSlots)
end Parent
namespace CurrentStock
export OriginalKBoundaryNativeSourceAction.Future (continuationFactory fromSourceSeed)
end CurrentStock
local instance residualGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
open OriginalKRawDualFeedbackSourceAction
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance residualBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target
local instance residualNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target

def continuationBeforeRawState := Parent.sourceSlotsRead (actualSourceValueRead t factory packet
 ((Parent.actualNextSourceFrame t factory packet).activeEnvironment () ()))

/-- This is the real full native input's difference from the preceding stored raw state, not a free identification of the two quantities. -/
def continuationInheritedRawChange := continuationNativeRawInput t factory packet-continuationBeforeRawState t factory packet

/-- This readout decomposes the full input without identifying it with the preceding raw state. -/
theorem continuation_actual_input_partition :
 continuationNativeRawInput t factory packet=continuationBeforeRawState t factory packet+continuationInheritedRawChange t factory packet := by
 unfold continuationInheritedRawChange
 abel

/-- Own signed feedback gives this budget for the complete actual native input, with no old-state or physical margin substitution. -/
theorem continuation_received_tail_bound :
 ‖(continuationReceivedRawState t factory packet).2.1‖≤(1/2:ℝ)*‖(continuationNativeRawInput t factory packet).2.1‖ ∧
 ‖(continuationReceivedRawState t factory packet).2.2‖≤(1/2:ℝ)*‖(continuationNativeRawInput t factory packet).2.2‖ := by
 rw [continuation_received_raw_source]
 constructor
 · exact le_trans (plusFeedback.le_opNorm _) (mul_le_mul_of_nonneg_right (source_feedback_norm).1 (norm_nonneg _))
 · exact le_trans (minusFeedback.le_opNorm _) (mul_le_mul_of_nonneg_right (source_feedback_norm).2 (norm_nonneg _))

/-- Every observer pays the actual inherited raw input before it reads this same whole's finite stock and complete tail. -/
theorem continuation_before_fee_keeps_inherited (test : BurnolQuarterMeanZeroCarrier) :
 let before:=continuationBeforeRawState t factory packet
 let inherited:=continuationInheritedRawChange t factory packet
 let received:=continuationReceivedRawState t factory packet
 inner ℂ (before.1.1+before.2.1) test+inner ℂ (inherited.1.1+inherited.2.1) test=
  inner ℂ received.1.1 test+inner ℂ received.2.1 test ∧
 inner ℂ (before.1.2+before.2.2) test+inner ℂ (inherited.1.2+inherited.2.2) test=
  inner ℂ received.1.2 test+inner ℂ received.2.2 test := by
 dsimp only
 have full:=continuation_received_full_raw_fee t factory packet test
 rw [continuation_actual_input_partition] at full
 constructor
 · simpa only [Prod.fst_add,Prod.snd_add,inner_add_left,add_assoc,add_left_comm,add_comm] using full.1
 · simpa only [Prod.fst_add,Prod.snd_add,inner_add_left,add_assoc,add_left_comm,add_comm] using full.2
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
