import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Carried
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (liftEvent)
end R
private theorem trace_map {X Y : Type u} (f : X → Y) (tree : RootedAccountedUnfolding X) :
 (tree.map f).trace=tree.trace.map f :=
 RootedAccountedUnfolding.rec
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
theorem input_carried_written {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)] {t : T}
 (input : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=A) (Var:=X) (sort:=t))
 (old : RootedAccountedUnfolding (PresentedRelationEventAt (Expr A X t)))
 (carried : input.inventory=some old) (event) (present : event ∈ old.trace) :
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent event ∈
 (Inventory.physicalWritten (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch input)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence input)).trace := by
 apply SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.complete_written_preserves
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.priorPairInventory
 change R.liftEvent event ∈ (match input.pairInventory with
  | none => SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftedInventory
    (Inventory.seed input) (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch input)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence input)
  | some carried => SourceHistoryCommon.seed carried
    (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftedInventory
      (Inventory.seed input) (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch input)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence input))).trace
 cases input.pairInventory with
 | none =>
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftedInventory
  rw [trace_map]
  apply List.mem_map.mpr
  refine ⟨event,?_,rfl⟩
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.priorSeed
  change event ∈ (match input.inventory with | none => _ | some carried => SourceHistoryCommon.seed _ carried).trace
  rw [carried]
  exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
 | some inherited =>
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftedInventory
  rw [trace_map]
  apply List.mem_map.mpr
  refine ⟨event,?_,rfl⟩
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.priorSeed
  change event ∈ (match input.inventory with | none => _ | some carried => SourceHistoryCommon.seed _ carried).trace
  rw [carried]
  exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

end SourceGeneratedInquiryReceiptAction.Inventory.Carried
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
