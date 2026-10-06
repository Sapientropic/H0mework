import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage : Nat)
theorem result_coordinate (index : Index frame configuration sourceStage stage) :
 (result frame configuration sourceStage stage).2.2.1 index=
 (C.term (expression frame configuration sourceStage stage) index).eval
  (mixedEnvironment (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)) :=
 (congrFun (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
  (Reverse.occurrence frame configuration sourceStage stage)) index).trans
 (SourceOperationExecution.Cochain.Inventory.coordinate _ _ _ index)
theorem ordered_equation : type_of% (SourceOperationExecution.Cochain.Inventory.complete_equation
 (expression frame configuration sourceStage stage) (Action.environment frame configuration sourceStage stage)
 (Action.increment frame configuration sourceStage stage)) := SourceOperationExecution.Cochain.Inventory.complete_equation _ _ _
theorem mixed_injective : Function.Injective (SourceOperationExecution.Cochain.Inventory.mixedIndex
 (expression frame configuration sourceStage stage)) := SourceOperationExecution.Cochain.Inventory.mixed_injective _
theorem mixed_read (index : Fin (expression frame configuration sourceStage stage).mixedTerms.length) :
 (result frame configuration sourceStage stage).2.2.1 (SourceOperationExecution.Cochain.Inventory.mixedIndex
  (expression frame configuration sourceStage stage) index)=
 ((expression frame configuration sourceStage stage).mixedTerms.get index).eval
 (mixedEnvironment (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)) :=
 result_coordinate frame configuration sourceStage stage _
private theorem read_equation {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)] {t : T}
 (expression : Expr A X t) (old change : Env A X)
 (answer : SourceOperationExecution.Cochain.Inventory.Index expression → A t)
 (value : answer=(SourceOperationExecution.Cochain.Inventory.query expression).eval
  (SourceOperationExecution.Cochain.Inventory.environment expression old change)) :
 answer (SourceOperationExecution.Cochain.Inventory.updatedIndex expression)=
 answer (SourceOperationExecution.Cochain.Inventory.oldIndex expression)+
 (List.ofFn (fun index : Fin expression.mixedTerms.length =>
  answer (SourceOperationExecution.Cochain.Inventory.mixedIndex expression index))).sum := by
 rw [value]
 exact SourceOperationExecution.Cochain.Inventory.complete_equation expression old change
theorem paid_equation : type_of% (read_equation (expression frame configuration sourceStage stage)
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)
 (result frame configuration sourceStage stage).2.2.1 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
  (Reverse.occurrence frame configuration sourceStage stage))) :=
 read_equation (expression frame configuration sourceStage stage)
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)
 (result frame configuration sourceStage stage).2.2.1 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
  (Reverse.occurrence frame configuration sourceStage stage))
theorem source_charge : (trace frame configuration sourceStage stage).length=
 InventoryVector.charge (Index frame configuration sourceStage stage)
 (SourceOperationExecution.Cochain.Inventory.items (expression frame configuration sourceStage stage)) :=
 SourceOperationExecution.Cochain.Inventory.charge _ _ _
theorem paid_charge : (result frame configuration sourceStage stage).2.1.2.length=
 InventoryVector.charge (Index frame configuration sourceStage stage)
 (SourceOperationExecution.Cochain.Inventory.items (expression frame configuration sourceStage stage)) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
 (InventoryVector.query_charge _ _)
theorem actual_reader : reader frame configuration sourceStage stage (Reverse.occurrence frame configuration sourceStage stage)=
 (sourceFace frame configuration sourceStage stage).rootRead.2.2.2 := rfl
theorem installed_result : (queryFace frame configuration sourceStage stage).rootRead=result frame configuration sourceStage stage := rfl
theorem source_ledger : (queryRoot frame configuration sourceStage stage).toAuthoritativeRoot.toLedgerRoot=
 (Reverse.original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem complete_written_born (event) (present : event ∈ (C.written (expression frame configuration sourceStage stage)
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)).trace) :
 Inventory.Born.migratedEvent (queryFrame frame configuration sourceStage stage)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme (Written.R.liftEvent event) ∈
 (Inventory.Born.inventory (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme).trace := by
 apply Inventory.Born.physical_event
 rw [Inventory.Born.original_physical_inventory]
 exact Inventory.Carried.input_carried_written _ _ rfl event present
theorem born_stock : type_of% (Inventory.Born.stock_source (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.stock_source _ _
theorem actual_disposition : type_of% (Inventory.Born.actual_disposition (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.actual_disposition _ _
theorem actual_query : type_of% (Inventory.Born.actual_query (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.actual_query _ _
theorem actual_inverse : type_of% (Inventory.Born.actual_inverse (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.actual_inverse _ _
theorem whole_first : type_of% (Inventory.Born.whole_first (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.whole_first _ _
theorem literal_next : type_of% (Inventory.Born.literal_next (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.literal_next _ _
theorem no_refill : type_of% (Inventory.Born.no_refill (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.no_refill _ _
theorem noetherian : type_of% (Inventory.Born.noetherian (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := Inventory.Born.noetherian _ _
abbrev nativeGenerated (nativeStage : Nat) := (Cochain.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
