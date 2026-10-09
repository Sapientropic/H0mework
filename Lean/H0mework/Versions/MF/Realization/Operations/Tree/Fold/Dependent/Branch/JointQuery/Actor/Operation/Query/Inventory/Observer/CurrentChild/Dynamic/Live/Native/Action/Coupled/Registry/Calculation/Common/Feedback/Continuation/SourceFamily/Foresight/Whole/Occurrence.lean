import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Whole.Facets
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Whole
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] groups
variable (binding : ∀ t, X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
def eventWord : PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s) → Word binding n data s
  | .generator expression => Finsupp.single expression 1
  | .relation word => word
def eventSource (event : PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)) :=
  fullMap binding n data s (eventWord binding n data event)
def sourceOccurrence : RootedAccountedUnfolding (Full binding n data s) :=
  match data.1.pairInventory with
  | none => RootedAccountedUnfolding.zero (rawSource binding n data)
  | some history => SourceHistoryCommon.seed
      (RootedAccountedUnfolding.zero (rawSource binding n data))
      (history.map (eventSource binding n data))
theorem occurrence_root : (sourceOccurrence binding n data).root = rawSource binding n data := by
  unfold sourceOccurrence
  cases data.1.pairInventory <;> rfl
theorem occurrence_keeps_inventory
    (history : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)))
    (actual : data.1.pairInventory = some history)
    (event) (present : event ∈ history.trace) :
    eventSource binding n data event ∈ (sourceOccurrence binding n data).trace := by
  have mapped : eventSource binding n data event ∈ (history.map (eventSource binding n data)).trace := by
    rw [T.mapped_trace]
    exact List.mem_map_of_mem present
  unfold sourceOccurrence
  rw [actual]
  exact (SourceHistoryCommon.parallel_right _ _ _).1 _ mapped
def occurrenceInput := {faceInput binding n data s (rawSource binding n data) with
  occurrence := sourceOccurrence binding n data}
def occurrenceFaces := UnifiedFourFace.generate (occurrenceInput binding n data)
theorem occurrence_dual : type_of% (UnifiedFourFace.generated_dual_readback (occurrenceInput binding n data)) :=
  UnifiedFourFace.generated_dual_readback _
def packetMaterial :=
  ((Lower.SourceFamily.Foresight.Elimination.face binding n data.2 data.1).rootRead,
   data.1.inventory, data.1.pairInventory, data.2, sourceOccurrence binding n data,
   occurrenceFaces binding n data)
theorem packet_material_original :
    (packetMaterial binding n data).1 =
      ((Lower.SourceFamily.Foresight.Elimination.face binding n data.2 data.1).rootRead) := rfl
theorem packet_history_original :
    (packetMaterial binding n data).2.2.1 = data.1.pairInventory ∧
    (packetMaterial binding n data).2.2.2.1 = data.2 := ⟨rfl,rfl⟩
end Lower.SourceFamily.Foresight.Whole
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
