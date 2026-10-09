import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Stock.Coordinates
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyTraceCoordinatesControls
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open RootInquiryCompletion CofinalHistorySettlement
namespace R
export SourceOperationInquiry.Context.Native.Frame.Stock.Return (written new_event_born)
end R
namespace B
export SourceGeneratedInquiryReceiptAction.Inventory.Born (inventory bornFrame consumer)
namespace V
export SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector (Index event word)
end V
namespace A
export SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual
 (actualFrame actualInventory intoActual actual_injective actual_event_read actual_word_read old_coordinate
  oldEnvironment increment occurrence reader root result first_whole first_next mother_whole mother_next)
end A
namespace C
export SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal
 (complete_word query_successor_field source_ledger installed_word installed_field installed_witness
  whole_first literal_next first_whole first_next paid_cost)
end C
end B
namespace P
export SourceOperationInquiry.Context.Native.Frame.Stock.Coordinates
 (intoBorn intoBorn_injective intoBorn_read intoBorn_strictMono source_exposure inventory_source)
end P
private theorem installed_state
 {N : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
 (old : SourceNativeAuthoritativeRootClosure N L)
 {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {sort : Sorts}
 (reader : {current : L.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
 {current : L.Current} (occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old reader occurrence).2.1=
 RootGeneratedDebtActivationJointSource.OwnerFree.Completion.completedState old current (fun _ => reader occurrence) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.target_state old current (fun _ => reader occurrence)

variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=W) (Var:=X) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))

def intoActual (index : Fin (R.written frame cfg).trace.length) :
 SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.ActualIndex frame cfg :=
 B.A.intoActual frame cfg (P.intoBorn frame cfg index)

theorem intoActual_injective : Function.Injective (intoActual frame cfg) :=
 (B.A.actual_injective frame cfg).comp (P.intoBorn_injective frame cfg)

theorem intoActual_read (index : Fin (R.written frame cfg).trace.length) :
 (B.A.actualInventory frame cfg).trace.get (intoActual frame cfg index)=
 (R.written frame cfg).trace.get index :=
 (B.A.actual_event_read frame cfg (P.intoBorn frame cfg index)).trans (P.intoBorn_read frame cfg index)

def completed : SourceOperationExecutionDebt.Settlement (B.A.result frame cfg).2.1 :=
 (installed_state (B.A.root frame cfg).toAuthoritativeRoot (B.A.reader frame cfg)
  (B.A.occurrence frame cfg)).symm ▸
 RootGeneratedDebtActivationJointSource.OwnerFree.Completion.completed
  (B.A.root frame cfg).toAuthoritativeRoot (B.A.actualFrame frame cfg).currentState.visit.current
  (fun _ => B.A.reader frame cfg (B.A.occurrence frame cfg))

theorem completed_value : (completed frame cfg).1=(B.A.result frame cfg).2.2.1 :=
 (SourceOperationExecutionDebt.completed_value _ (completed frame cfg)).trans
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
   (B.A.root frame cfg).toAuthoritativeRoot (B.A.reader frame cfg) (B.A.occurrence frame cfg)).symm

theorem indexed_update (index : Fin (R.written frame cfg).trace.length) :
 (B.A.result frame cfg).2.2.1 (intoActual frame cfg index)=
 updateInventory (R:=ℤ) (B.A.oldEnvironment frame cfg (B.A.occurrence frame cfg))
  (B.A.increment frame cfg (B.A.occurrence frame cfg))
  (SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.inventoryEventWord cfg
   ((R.written frame cfg).trace.get index)) :=
 (B.A.old_coordinate frame cfg (P.intoBorn frame cfg index)).trans
  (congrArg (updateInventory (R:=ℤ) (B.A.oldEnvironment frame cfg (B.A.occurrence frame cfg))
    (B.A.increment frame cfg (B.A.occurrence frame cfg)))
   (congrArg (SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.inventoryEventWord cfg)
    (P.intoBorn_read frame cfg index)))

theorem different_positions {i j : Fin (R.written frame cfg).trace.length} (different : i≠j) :
 intoActual frame cfg i≠intoActual frame cfg j :=
 fun same => different (intoActual_injective frame cfg same)

theorem same_value_distinct_positions {i j : Fin (R.written frame cfg).trace.length}
 (different : i≠j) (same : (R.written frame cfg).trace.get i=(R.written frame cfg).trace.get j) :
 intoActual frame cfg i≠intoActual frame cfg j ∧
 (B.A.actualInventory frame cfg).trace.get (intoActual frame cfg i)=
 (B.A.actualInventory frame cfg).trace.get (intoActual frame cfg j) :=
 ⟨different_positions frame cfg different,
  (intoActual_read frame cfg i).trans (same.trans (intoActual_read frame cfg j).symm)⟩

theorem cofinal_word (stage : Nat) : type_of% (B.C.complete_word frame cfg stage) := B.C.complete_word frame cfg stage

theorem cofinal_next (stage : Nat) : type_of% (B.C.query_successor_field frame cfg stage) :=
 B.C.query_successor_field frame cfg stage

theorem cofinal_ledger (stage : Nat) : type_of% (B.C.source_ledger frame cfg stage) := B.C.source_ledger frame cfg stage

theorem actual_whole : type_of% (B.A.first_whole frame cfg) := B.A.first_whole frame cfg

theorem actual_math_next : type_of% (B.A.first_next frame cfg) := B.A.first_next frame cfg

theorem cofinal_whole (stage : Nat) : type_of% (B.C.whole_first frame cfg stage) := B.C.whole_first frame cfg stage

theorem cofinal_math_next (stage : Nat) : type_of% (B.C.literal_next frame cfg stage) := B.C.literal_next frame cfg stage

#print axioms P.source_exposure
#print axioms P.inventory_source
#print axioms P.intoBorn_injective
#print axioms P.intoBorn_read
#print axioms P.intoBorn_strictMono
#print axioms intoActual_injective
#print axioms intoActual_read
#print axioms completed
#print axioms completed_value
#print axioms indexed_update
#print axioms same_value_distinct_positions
#print axioms cofinal_word
#print axioms cofinal_next
#print axioms cofinal_ledger
#print axioms actual_whole
#print axioms actual_math_next
#print axioms cofinal_whole
#print axioms cofinal_math_next
end SourcePolicyTraceCoordinatesControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
