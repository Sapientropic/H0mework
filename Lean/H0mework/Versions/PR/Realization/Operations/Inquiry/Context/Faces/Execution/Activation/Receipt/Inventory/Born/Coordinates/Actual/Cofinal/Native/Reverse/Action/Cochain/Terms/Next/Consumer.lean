import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement SourceGeneratedScalarDifferentialResidual
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage : Nat)
theorem actual_binding : (fun sort name => (binding frame configuration sourceStage stage sort name).eval
 (environment frame configuration sourceStage stage))=nextEnvironment frame configuration sourceStage stage :=
 M.vector_next (Reverse.runtime frame configuration sourceStage) (Reverse.source frame configuration sourceStage)
 (Index frame configuration sourceStage stage) (Action.state frame configuration sourceStage stage)
theorem actual_value : (result frame configuration sourceStage stage).2.2.1=
 (Terms.raw frame configuration sourceStage stage).expression.eval (nextEnvironment frame configuration sourceStage stage) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
  (Reverse.occurrence frame configuration sourceStage stage)).trans
 (((Terms.raw frame configuration sourceStage stage).expression.eval_subst
   (binding frame configuration sourceStage stage) (environment frame configuration sourceStage stage)).trans
 (congrArg (Terms.raw frame configuration sourceStage stage).expression.eval (actual_binding frame configuration sourceStage stage)))
theorem next_coordinate (index : Index frame configuration sourceStage stage) :
 (result frame configuration sourceStage stage).2.2.1 index=
 (Terms.C.term (Terms.expression frame configuration sourceStage stage) index).eval
  (M.environment (Reverse.runtime frame configuration sourceStage) (Reverse.source frame configuration sourceStage)
   (nextState frame configuration sourceStage stage)) :=
 (congrFun (actual_value frame configuration sourceStage stage) index).trans
  (SourceOperationExecution.Cochain.Inventory.coordinate (Terms.expression frame configuration sourceStage stage)
   (Action.P.environment (Reverse.runtime frame configuration sourceStage) (Reverse.source frame configuration sourceStage)
    (SourceOperationInquiry.point _ (nextState frame configuration sourceStage stage)))
   (Action.P.environment (Reverse.runtime frame configuration sourceStage) (Reverse.source frame configuration sourceStage)
    (SourceOperationInquiry.point _ (nextState frame configuration sourceStage stage).tick.nextState-
     SourceOperationInquiry.point _ (nextState frame configuration sourceStage stage))) index)
private theorem inverse_value {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)] {t : T}
 (env : Env A X) (expression : Expr A X t) :
 (residualEquivRange (evaluation (R:=ℤ) env)
  (canonicalResidual (evaluation (R:=ℤ) env) (Finsupp.single expression 1))).val=expression.eval env := by
 change evaluation (R:=ℤ) env (Finsupp.single expression 1)=_
 exact (Finsupp.linearCombination_single _ _ _).trans (one_smul _ _)
theorem inverse_read : (result frame configuration sourceStage stage).2.2.1=
 (residualEquivRange (evaluation (R:=ℤ) (nextEnvironment frame configuration sourceStage stage))
  (inverse frame configuration sourceStage stage)).val :=
 (actual_value frame configuration sourceStage stage).trans (inverse_value _ _).symm
theorem paid_charge : (result frame configuration sourceStage stage).2.1.2.length=remaining (raw frame configuration sourceStage stage).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem actual_reader : reader frame configuration sourceStage stage (Reverse.occurrence frame configuration sourceStage stage)=
 (sourceFace frame configuration sourceStage stage).rootRead.2.2.2 := rfl
theorem installed_result : (queryFace frame configuration sourceStage stage).rootRead=result frame configuration sourceStage stage := rfl
theorem source_ledger : (queryRoot frame configuration sourceStage stage).toAuthoritativeRoot.toLedgerRoot=
 (Reverse.original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem complete_written_born (event) (present : event ∈ (SourceOperationPaidRelations.exposure
 (result frame configuration sourceStage stage).2.1.2).trace) :
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
abbrev nativeGenerated (nativeStage : Nat) := (Terms.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
