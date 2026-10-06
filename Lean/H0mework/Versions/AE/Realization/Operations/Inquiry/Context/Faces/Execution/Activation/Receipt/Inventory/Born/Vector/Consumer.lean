import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Vector.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
variable (supplied : C.Occurrence (bornFrame frame configuration) (current:=current))
theorem raw_coordinate (index : Index frame configuration) :
 (raw frame configuration supplied).expression.eval (raw frame configuration supplied).environment index=
 updateInventory (R:=ℤ) (oldEnvironment frame configuration supplied) (increment frame configuration supplied)
  (word frame configuration index) := by
 have read := V.query_read (Index frame configuration) (items frame configuration)
  (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) index
 have single : ((items frame configuration).map (fun item => if index=item.1 then
   item.2.eval (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) else 0)).sum=
  (liftExpr (SourceOperationExecution.Coefficients.expression (word frame configuration index))).eval
   (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) := by
  simp only [items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_ite_eq (s:=Finset.univ) index
   (fun coordinate : Index frame configuration =>
    (liftExpr (SourceOperationExecution.Coefficients.expression (word frame configuration coordinate))).eval
     (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)))
   |>.trans (if_pos (Finset.mem_univ index))
 exact read.trans (single.trans ((eval_liftExpr _ _ _).trans
  (congrArg₂ Prod.mk (SourceOperationExecution.Coefficients.expression_eval _ _)
   (SourceOperationExecution.Coefficients.expression_effect _ _ _))))
theorem result_coordinate (index : Index frame configuration) :
 (result frame configuration).2.2.1 index=
 updateInventory (R:=ℤ) (oldEnvironment frame configuration (occurrence frame configuration))
  (increment frame configuration (occurrence frame configuration)) (word frame configuration index) :=
 congrFun (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (sourceRoot frame configuration).toAuthoritativeRoot (reader frame configuration) (occurrence frame configuration)) index
  |>.trans (raw_coordinate frame configuration (occurrence frame configuration) index)
theorem installed_result : (queryFace frame configuration).rootRead=result frame configuration := rfl
theorem paid_cost : (result frame configuration).2.1.2.length=
 SaturationMonoid.SourceOperationExecution.InventoryVector.charge (Index frame configuration) (items frame configuration) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans (V.query_charge _ _)
theorem whole_inventory_zero : (result frame configuration).2.2.1=0 ↔
 ∀ index : Index frame configuration,
  updateInventory (R:=ℤ) (oldEnvironment frame configuration (occurrence frame configuration))
   (increment frame configuration (occurrence frame configuration)) (word frame configuration index)=0 := by
 constructor
 · intro zero index
   exact (result_coordinate frame configuration index).symm.trans (congrFun zero index)
 · intro zero
   funext index
   exact (result_coordinate frame configuration index).trans (zero index)
theorem next_coordinate (index : Index frame configuration) :
 ((result frame configuration).2.2.1 index).1 + ((result frame configuration).2.2.1 index).2=
 evaluation (R:=ℤ) (physical frame configuration (occurrence frame configuration)).nextRaw.environment
  (word frame configuration index) := by
 rw [result_coordinate]
 exact (LinearMap.congr_fun (evaluation_update (R:=ℤ)
  (oldEnvironment frame configuration (occurrence frame configuration))
  (increment frame configuration (occurrence frame configuration))) (word frame configuration index)).symm.trans
  (congrArg (fun environment => evaluation (R:=ℤ) environment (word frame configuration index)) (add_sub_cancel _ _))
theorem source_ledger : (queryRoot frame configuration).toAuthoritativeRoot.toLedgerRoot=
 (sourceRoot frame configuration).toAuthoritativeRoot.toLedgerRoot := rfl
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (queryRoot frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (queryRoot frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
theorem mother_whole : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) :=
 SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem mother_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) :=
 SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem runtime_next (stage : Nat) : type_of% (SourceGeneratedInquiryReceiptAction.runtime_next (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme stage) :=
 SourceGeneratedInquiryReceiptAction.runtime_next _ _ stage
abbrev nativeGenerated (stage : Nat) := (Born.nativeGenerated frame configuration stage,
 generated (Faces.Native.nativeFrame frame configuration stage) Faces.Native.R.programme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
