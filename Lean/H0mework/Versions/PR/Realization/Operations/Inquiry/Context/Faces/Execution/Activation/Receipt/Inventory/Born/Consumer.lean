import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (materialFace actual_query actual_disposition whole_first_write literal_next independent_updated_inverse
  complete_written_preserves birthTransition)
end J
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (priorSeed updatedSeed physical disposition materialFace history)
end P
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence nextBorn)
end Shared
private theorem trace_map {X Y : Type u} (f : X → Y) (tree : RootedAccountedUnfolding X) :
 (tree.map f).trace=tree.trace.map f := by
 exact RootedAccountedUnfolding.rec
  (motive_1:=fun current => (current.map f).trace=current.trace.map f)
  (motive_2:=fun branches => RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches f branches)=
    (RootedAccountedUnfolding.traceBranches branches).map f)
  (fun root branches previous => by
   simp only [RootedAccountedUnfolding.map,RootedAccountedUnfolding.trace,List.map_cons]
   exact congrArg (List.cons (f root)) previous)
  (by simp only [RootedAccountedUnfolding.mapBranches,RootedAccountedUnfolding.traceBranches,List.map_nil])
  (fun head tail headProof tailProof => by
   simp only [RootedAccountedUnfolding.mapBranches,RootedAccountedUnfolding.traceBranches,List.map_append]
   exact AccountedList.congrArgTwo List.append headProof tailProof) tree
theorem physical_event (event) (present : event ∈ (physicalInventory frame configuration).trace) :
 migratedEvent frame configuration event ∈ (inventory frame configuration).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 rw [trace_map]
 exact List.mem_map.mpr ⟨event,present,rfl⟩
theorem low_event (event) (present : event ∈ (lowInventory frame configuration).trace) :
 event ∈ (inventory frame configuration).trace := (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem binding_environment : (fun target name => (binding frame configuration target name).eval
 (lowRaw frame configuration).environment)=(physicalRaw frame configuration).environment := by
 unfold binding lowRaw physicalRaw
 rw [stock_source]
 rfl
theorem original_expression (expression : Expr (PairValue PhysicalValue) PhysicalVar slot) :
 (expression.subst (binding frame configuration)).eval (lowRaw frame configuration).environment=
 expression.eval (physicalRaw frame configuration).environment :=
 (expression.eval_subst _ _).trans (congrArg expression.eval (binding_environment frame configuration))
theorem original_relation (word : Formal ℤ (PairValue PhysicalValue) PhysicalVar slot) :
 evaluation (R:=ℤ) (lowRaw frame configuration).environment (substitution (R:=ℤ) (binding frame configuration) word)=
 evaluation (R:=ℤ) (physicalRaw frame configuration).environment word := by
 have square := LinearMap.congr_fun (evaluation_substitution (R:=ℤ) (s:=slot)
  (binding frame configuration) (lowRaw frame configuration).environment) word
 exact square.trans (congrArg (fun environment => evaluation (R:=ℤ) environment word) (binding_environment frame configuration))
theorem born_occurrence : (bornFrame frame configuration).currentState=
 SourceGeneratedInquiryReceiptAction.targetState frame (programme configuration) := rfl
theorem cofinal_input (event) (present : event ∈ (inventory frame configuration).trace) :
 event ∈ (P.updatedSeed (seed frame configuration) (A.epoch (bornFrame frame configuration))
  (Shared.actualOccurrence (bornFrame frame configuration))).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 change event ∈ (SourceHistoryCommon.seed (seed frame configuration) (inventory frame configuration)).trace
 exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem actual_disposition : (P.materialFace (seed frame configuration) (bornFrame frame configuration)).rootRead.2.2.2.1=
 P.disposition (seed frame configuration) (A.epoch (bornFrame frame configuration))
  (Shared.actualOccurrence (bornFrame frame configuration)) := rfl
theorem actual_query : type_of% (J.actual_query (seed frame configuration) (bornFrame frame configuration)) :=
 J.actual_query (seed frame configuration) (bornFrame frame configuration)
theorem next_inventory (event) (present : event ∈ (inventory frame configuration).trace) :
 event ∈ (P.updatedSeed (seed frame configuration)
  (A.epoch (Shared.nextBorn (bornFrame frame configuration) (consumer frame configuration)))
  (Shared.actualOccurrence (Shared.nextBorn (bornFrame frame configuration) (consumer frame configuration)))).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 change event ∈ (SourceHistoryCommon.seed (seed frame configuration)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.relationWrite
   (seed frame configuration) (A.epoch (bornFrame frame configuration))
   (Shared.actualOccurrence (bornFrame frame configuration))
   (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.disposition
    (seed frame configuration) (A.epoch (bornFrame frame configuration))
    (Shared.actualOccurrence (bornFrame frame configuration))))).trace
 apply (SourceHistoryCommon.parallel_right _ _ _).1
 exact SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.relation_write_preserves
  (seed frame configuration) (A.epoch (bornFrame frame configuration))
  (Shared.actualOccurrence (bornFrame frame configuration)) _ event (cofinal_input frame configuration event present)
theorem original_physical_inventory : physicalInventory frame configuration=
 Inventory.physicalWritten (A.epoch frame) (A.Shared.actualOccurrence frame) := by
 unfold physicalInventory
 rw [stock_source]
 rfl
theorem original_low_inventory : lowInventory frame configuration=
 completeWritten (A.epoch frame) configuration (A.Shared.actualOccurrence frame) := by
 unfold lowInventory
 rw [stock_source]
 rfl
theorem whole_first : type_of% (SourceGeneratedInquiryReceiptAction.whole_first
 (bornFrame frame configuration) (consumer frame configuration)) :=
 SourceGeneratedInquiryReceiptAction.whole_first (bornFrame frame configuration) (consumer frame configuration)
theorem literal_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next
 (bornFrame frame configuration) (consumer frame configuration)) :=
 SourceGeneratedInquiryReceiptAction.literal_next (bornFrame frame configuration) (consumer frame configuration)
theorem actual_update : type_of% (SourceGeneratedInquiryReceiptAction.actual_updated_environment
 (bornFrame frame configuration) (consumer frame configuration)) :=
 SourceGeneratedInquiryReceiptAction.actual_updated_environment (bornFrame frame configuration) (consumer frame configuration)
theorem actual_inverse : type_of% (SourceGeneratedInquiryReceiptAction.source_inverse
 (bornFrame frame configuration) (consumer frame configuration)) :=
 SourceGeneratedInquiryReceiptAction.source_inverse (bornFrame frame configuration) (consumer frame configuration)
theorem runtime_next (stage : Nat) : type_of% (SourceGeneratedInquiryReceiptAction.runtime_next
 (bornFrame frame configuration) (consumer frame configuration) stage) :=
 SourceGeneratedInquiryReceiptAction.runtime_next (bornFrame frame configuration) (consumer frame configuration) stage
theorem no_refill : type_of% (SourceGeneratedInquiryReceiptAction.no_refill
 (bornFrame frame configuration) (consumer frame configuration)) :=
 SourceGeneratedInquiryReceiptAction.no_refill (bornFrame frame configuration) (consumer frame configuration)
theorem noetherian : type_of% (SourceGeneratedInquiryReceiptAction.noetherian
 (bornFrame frame configuration) (consumer frame configuration)) :=
 SourceGeneratedInquiryReceiptAction.noetherian (bornFrame frame configuration) (consumer frame configuration)
abbrev nativeGenerated (stage : Nat) :=
 (Inventory.nativeGenerated frame configuration stage,
  generated (Faces.Native.nativeFrame frame configuration stage) Faces.Native.R.programme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
