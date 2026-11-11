import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Receipt
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Action
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
local instance receivedGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance receivedBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target
local instance receivedNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target

def continuationNativeRawInput := Parent.sourceSlotsRead
 (actualNativeTotalRead t factory packet (continuationSourceUpdatedTotal t factory packet))
def continuationReceivedSourceValue := actualNativeTotalRead t factory packet
 ((continuationSourceBorn t factory packet).activeEnvironment () ())
def continuationReceivedRawState := Parent.sourceSlotsRead (continuationReceivedSourceValue t factory packet)

/-- The actual born environment reads its own full receipt total, then the literal source action generates the next raw state. -/
theorem continuation_received_raw_source :
 continuationReceivedRawState t factory packet=Parent.sourceFeedbackNext (continuationNativeRawInput t factory packet) := by
 unfold continuationReceivedRawState continuationReceivedSourceValue
 have environment := Environment.active (continuation_actual_born_environment t factory packet)
 rw [environment,actual_literal_source_action]
 unfold OriginalKSourceFeedbackSuccessorAction.sourceSlotNext
 exact OriginalKSourceFeedbackSuccessorAction.source_slots_recover_raw _

/-- Complete finite-plus-tail prices consume the actually received raw field, preserving its same native input quantity. -/
theorem continuation_received_full_raw_fee (test : BurnolQuarterMeanZeroCarrier) :
 let raw:=continuationNativeRawInput t factory packet
 let received:=continuationReceivedRawState t factory packet
 inner ℂ (raw.1.1+raw.2.1) test=inner ℂ received.1.1 test+inner ℂ received.2.1 test ∧
 inner ℂ (raw.1.2+raw.2.2) test=inner ℂ received.1.2 test+inner ℂ received.2.2 test := by
 dsimp only
 rw [continuation_received_raw_source]
 have actual:=OriginalKSourceFeedbackSuccessorAction.source_feedback_whole_conserved (continuationNativeRawInput t factory packet)
 constructor
 · rw [←actual.1,inner_add_left]
 · rw [←actual.2,inner_add_left]
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
