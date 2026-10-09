import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Consumer
import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Inventory.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Outgoing.Consumer
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Source
import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Consumer
import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
 (actual_query actual_input completed_value paid_history actual_next actual_answer)
end A
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (updatedSeed supplied_seed_preserved)
end P
namespace F4
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace
 (dual_readback complete_fibre cofinal_next source_equation macro_payment no_refill noetherian rawSource)
end F4
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
theorem receipt_whole : type_of% (SourceGeneratedInquiryReceiptAction.whole_first
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)) :=
 SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem receipt_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) (programme root visit recognition U7 calculus anchor sourceStage)) :=
 SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem initial_stock : (lowInitial root visit recognition U7 calculus anchor sourceStage stage).inventory=
 some (lowWritten root visit recognition U7 calculus anchor sourceStage stage) := rfl
theorem actual_initial : (lowRuntime root visit recognition U7 calculus anchor sourceStage stage).initialState.engine.node=
 .active (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation (lowInitial root visit recognition U7 calculus anchor sourceStage stage)
  (lowProgramme root visit recognition U7 calculus anchor sourceStage stage)) := rfl
theorem exact_current : (lowInitial root visit recognition U7 calculus anchor sourceStage stage).currentState=
 SourceGeneratedInquiryReceiptAction.targetState (frameAt root visit recognition U7 calculus anchor sourceStage stage)
  (programme root visit recognition U7 calculus anchor sourceStage) := rfl
theorem stock_preserved (offset : Nat) (event)
 (present : event ∈ (lowStock root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (lowFace root visit recognition U7 calculus anchor sourceStage stage offset).rootRead.1.1.1.1.2.1.trace := by
 change event ∈ (P.updatedSeed (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
  (E.epoch (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset))
  (E.Shared.actualOccurrence (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset))).trace
 have inWritten : event ∈ (lowWritten root visit recognition U7 calculus anchor sourceStage stage).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
 have inSeed : event ∈ (lowSeed root visit recognition U7 calculus anchor sourceStage stage).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event inWritten
 exact P.supplied_seed_preserved (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
  (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset) event inSeed
theorem initial_pair : (lowInitial root visit recognition U7 calculus anchor sourceStage stage).pairInventory=
 some (lowPairWritten root visit recognition U7 calculus anchor sourceStage stage) := rfl
theorem written_preserved (offset : Nat) (event)
 (present : event ∈ (lowWritten root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (lowFace root visit recognition U7 calculus anchor sourceStage stage offset).rootRead.1.1.1.1.2.1.trace := by
 change event ∈ (P.updatedSeed (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
  (E.epoch (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset))
  (E.Shared.actualOccurrence (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset))).trace
 have inSeed : event ∈ (lowSeed root visit recognition U7 calculus anchor sourceStage stage).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
 exact P.supplied_seed_preserved (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
  (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset) event inSeed
theorem outgoing_scalar_preserved (offset : Nat) (event)
 (present : event ∈ (outgoingScalar root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (lowFace root visit recognition U7 calculus anchor sourceStage stage offset).rootRead.1.1.1.1.2.1.trace :=
 written_preserved root visit recognition U7 calculus anchor sourceStage stage offset event
  ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem initial_outgoing_pair (event)
 (present : event ∈ (outgoingPair root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (lowPairWritten root visit recognition U7 calculus anchor sourceStage stage).trace :=
 SourceGeneratedInquiryReceiptAction.Configured.pair_event_preserved
  (frameAt root visit recognition U7 calculus anchor sourceStage stage)
  (programme root visit recognition U7 calculus anchor sourceStage) event present
theorem delta_scalar_preserved (offset : Nat) (event)
 (present : event ∈ (SourceOperationInquiry.Context.Outgoing.scalarExposure
  (frameAt root visit recognition U7 calculus anchor sourceStage stage)
  (programme root visit recognition U7 calculus anchor sourceStage)).trace) :
 event ∈ (lowFace root visit recognition U7 calculus anchor sourceStage stage offset).rootRead.1.1.1.1.2.1.trace :=
 outgoing_scalar_preserved root visit recognition U7 calculus anchor sourceStage stage offset event
  (SourceOperationInquiry.Context.Outgoing.scalar_preserved _ _ event present)
theorem next_syntax_preserved (offset : Nat) (event)
 (present : event ∈ (SourceOperationInquiry.Context.Outgoing.nextSyntaxExposure
  (frameAt root visit recognition U7 calculus anchor sourceStage stage)
  (programme root visit recognition U7 calculus anchor sourceStage)).trace) :
 event ∈ (lowFace root visit recognition U7 calculus anchor sourceStage stage offset).rootRead.1.1.1.1.2.1.trace :=
 outgoing_scalar_preserved root visit recognition U7 calculus anchor sourceStage stage offset event
  (SourceOperationInquiry.Context.Outgoing.next_preserved _ _ event present)
namespace Pair
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Inventory
 (pairStock prior_pair_preserved full_pair_inventory)
end Pair
theorem outgoing_pair_preserved (offset : Nat) (event)
 (present : event ∈ (outgoingPair root visit recognition U7 calculus anchor sourceStage stage).trace) :
 event ∈ (Pair.pairStock (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
  (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset)).trace := by
 exact Pair.full_pair_inventory (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
  (lowInitial root visit recognition U7 calculus anchor sourceStage stage)
  (lowPairWritten root visit recognition U7 calculus anchor sourceStage stage) rfl offset event
  (initial_outgoing_pair root visit recognition U7 calculus anchor sourceStage stage event present)
theorem actual_disposition (offset : Nat) : (lowFace root visit recognition U7 calculus anchor sourceStage stage offset).rootRead.1.2.2.2.1=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.disposition
  (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
  (E.epoch (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset))
  (E.Shared.actualOccurrence (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset)) := rfl
theorem actual_query (offset : Nat) : type_of% (A.actual_input
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
 (lowInitial root visit recognition U7 calculus anchor sourceStage stage) offset) := A.actual_input _ _ offset
theorem actual_result (offset : Nat) : type_of% (A.completed_value
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
 (lowFrameAt root visit recognition U7 calculus anchor sourceStage stage offset)) := A.completed_value _ _
theorem actual_next (offset : Nat) : type_of% (A.actual_next
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
 (lowInitial root visit recognition U7 calculus anchor sourceStage stage) offset) := A.actual_next _ _ offset
theorem four_faces (offset : Nat) : type_of% (F4.dual_readback
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
 (lowInitial root visit recognition U7 calculus anchor sourceStage stage) offset) := F4.dual_readback _ _ offset
theorem source_equation (offset : Nat) : type_of% (F4.source_equation
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
 (lowInitial root visit recognition U7 calculus anchor sourceStage stage) offset) := F4.source_equation _ _ offset
theorem macro_payment (offset : Nat) : type_of% (F4.macro_payment
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
 (lowInitial root visit recognition U7 calculus anchor sourceStage stage) offset) := F4.macro_payment _ _ offset
theorem noetherian (offset : Nat) : type_of% (F4.noetherian
 (lowSeed root visit recognition U7 calculus anchor sourceStage stage)
 (lowInitial root visit recognition U7 calculus anchor sourceStage stage) offset) := F4.noetherian _ _ offset
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
