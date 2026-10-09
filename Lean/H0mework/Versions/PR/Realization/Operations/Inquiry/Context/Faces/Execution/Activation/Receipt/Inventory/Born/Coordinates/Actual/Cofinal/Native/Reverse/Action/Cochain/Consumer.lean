import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain
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
theorem generated_relation : type_of% (SourceOperationExecution.Cochain.generated_boundary
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)
 (Action.boundary frame configuration sourceStage stage)) := SourceOperationExecution.Cochain.generated_boundary _ _ _
theorem query_zero : (result frame configuration sourceStage stage).2.2.1=0 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
  (Reverse.occurrence frame configuration sourceStage stage)).trans
 (SourceOperationExecution.Cochain.source_zero _ _ _)
theorem source_charge : (trace frame configuration sourceStage stage).length=
 SourceOperationExecution.Coefficients.cost (C.boundary (Action.boundary frame configuration sourceStage stage)) :=
 SourceOperationExecution.Cochain.complete_charge _ _ _
theorem paid_charge : (result frame configuration sourceStage stage).2.1.2.length=
 SourceOperationExecution.Coefficients.cost (C.boundary (Action.boundary frame configuration sourceStage stage)) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
 (SourceOperationExecution.Coefficients.expression_remaining _)
theorem complete_steps : type_of% (SourceOperationExecution.Cochain.complete_steps
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)
 (Action.boundary frame configuration sourceStage stage)) := SourceOperationExecution.Cochain.complete_steps _ _ _
theorem actual_reader : reader frame configuration sourceStage stage (Reverse.occurrence frame configuration sourceStage stage)=
 (sourceFace frame configuration sourceStage stage).rootRead.2.2.2.2 := rfl
theorem installed_result : (queryFace frame configuration sourceStage stage).rootRead=result frame configuration sourceStage stage := rfl
theorem source_ledger : (queryRoot frame configuration sourceStage stage).toAuthoritativeRoot.toLedgerRoot=
 (Reverse.original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem complete_written_born (event) (present : event ∈ (C.written
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)
 (Action.boundary frame configuration sourceStage stage)).trace) :
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
abbrev nativeGenerated (nativeStage : Nat) := (Written.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
