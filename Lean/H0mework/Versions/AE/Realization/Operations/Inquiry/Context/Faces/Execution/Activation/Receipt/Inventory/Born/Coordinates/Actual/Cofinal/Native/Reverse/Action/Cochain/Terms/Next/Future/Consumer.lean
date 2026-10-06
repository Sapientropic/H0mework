import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count : Nat)
namespace F
export SourceOperationInquiry.Context.Faces.Cofinal (complete_word_readback relation_zero_iff relation_read relation_next_read)
end F
theorem complete_word : type_of% (F.complete_word_readback (runtime frame configuration sourceStage stage)
 (source frame configuration sourceStage stage) count) := F.complete_word_readback _ _ count
theorem complete_future_zero : type_of% (F.relation_zero_iff (runtime frame configuration sourceStage stage)
 (source frame configuration sourceStage stage) count) := F.relation_zero_iff _ _ count
theorem actual_prefix (bound : Nat) (index : Fin (bound+1)) : type_of% (F.relation_read
 (runtime frame configuration sourceStage stage) (source frame configuration sourceStage stage) count bound index) :=
 F.relation_read _ _ count bound index
theorem actual_future_next (bound : Nat) (index : Fin (bound+1)) : type_of% (F.relation_next_read
 (runtime frame configuration sourceStage stage) (source frame configuration sourceStage stage) count bound index) :=
 F.relation_next_read _ _ count bound index
theorem actual_query : type_of% (J.queryAt (seed frame configuration sourceStage stage)
 (initial frame configuration sourceStage stage) count) := J.queryAt _ _ count
theorem actual_answer : type_of% (J.answerAt (seed frame configuration sourceStage stage)
 (initial frame configuration sourceStage stage) count) := J.answerAt _ _ count
theorem actual_next : type_of% (J.nextAt (seed frame configuration sourceStage stage)
 (initial frame configuration sourceStage stage) count) := J.nextAt _ _ count
theorem complete_inventory (distance : Nat) : type_of% (J.full_scalar_inventory
 (seed frame configuration sourceStage stage) (initial frame configuration sourceStage stage) count distance) :=
 J.full_scalar_inventory _ _ count distance
theorem no_refill : type_of% (J.no_refill (seed frame configuration sourceStage stage)
 (initial frame configuration sourceStage stage) count) := J.no_refill _ _ count
theorem noetherian : type_of% (J.noetherian (seed frame configuration sourceStage stage)
 (initial frame configuration sourceStage stage) count) := J.noetherian _ _ count
variable (queryCount : Nat)
theorem next_query_field : type_of% (Actual.Cofinal.query_successor_field
 (frameAt frame configuration sourceStage stage count) (consumer frame configuration sourceStage stage) queryCount) :=
 Actual.Cofinal.query_successor_field _ _ queryCount
theorem next_query_whole : type_of% (Actual.Cofinal.whole_first
 (frameAt frame configuration sourceStage stage count) (consumer frame configuration sourceStage stage) queryCount) :=
 Actual.Cofinal.whole_first _ _ queryCount
theorem next_query_literal_next : type_of% (Actual.Cofinal.literal_next
 (frameAt frame configuration sourceStage stage count) (consumer frame configuration sourceStage stage) queryCount) :=
 Actual.Cofinal.literal_next _ _ queryCount
abbrev nativeGenerated (nativeStage : Nat) := (Next.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
