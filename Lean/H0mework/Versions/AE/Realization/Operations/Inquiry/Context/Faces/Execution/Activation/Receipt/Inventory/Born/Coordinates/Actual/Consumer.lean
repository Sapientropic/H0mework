import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Query
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (actualFrame frame configuration).registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence (actualFrame frame configuration) (current:=current))
private theorem nextFrom_actual (sourceFrame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot)) :
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next sourceFrame (consumer frame configuration)=
 nextFrom frame configuration sourceFrame sourceFrame.action := by
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next nextFrom
 cases sourceFrame.action <;> rfl
theorem actual_frame : actualFrame frame configuration=nextFrom frame configuration (bornFrame frame configuration)
 (bornFrame frame configuration).action := nextFrom_actual frame configuration (bornFrame frame configuration)
theorem actual_inventory : actualInventory frame configuration=inventoryAt frame configuration (actualFrame frame configuration) :=
 congrArg (inventoryAt frame configuration) (actual_frame frame configuration).symm
theorem raw_coordinate (index : ActualIndex frame configuration) :
 (raw frame configuration supplied).expression.eval (raw frame configuration supplied).environment index=
 updateInventory (R:=ℤ) (oldEnvironment frame configuration supplied) (increment frame configuration supplied)
  (actualWord frame configuration index) := by
 have read := SaturationMonoid.SourceOperationExecution.InventoryVector.query_read (ActualIndex frame configuration)
  (items frame configuration) (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) index
 have single : ((items frame configuration).map (fun item => if index=item.1 then
   item.2.eval (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) else 0)).sum=
  (liftExpr (SourceOperationExecution.Coefficients.expression (actualWord frame configuration index))).eval
   (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) := by
  simp only [items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_ite_eq (s:=Finset.univ) index
   (fun coordinate : ActualIndex frame configuration =>
    (liftExpr (SourceOperationExecution.Coefficients.expression (actualWord frame configuration coordinate))).eval
     (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)))
   |>.trans (if_pos (Finset.mem_univ index))
 exact read.trans (single.trans ((eval_liftExpr _ _ _).trans
  (congrArg₂ Prod.mk (SourceOperationExecution.Coefficients.expression_eval _ _)
   (SourceOperationExecution.Coefficients.expression_effect _ _ _))))
theorem result_coordinate (index : ActualIndex frame configuration) :
 (result frame configuration).2.2.1 index=
 updateInventory (R:=ℤ) (oldEnvironment frame configuration (occurrence frame configuration))
  (increment frame configuration (occurrence frame configuration)) (actualWord frame configuration index) :=
 congrFun (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (root frame configuration).toAuthoritativeRoot (reader frame configuration) (occurrence frame configuration)) index
  |>.trans (raw_coordinate frame configuration (occurrence frame configuration) index)
theorem old_coordinate (index : Vector.Index frame configuration) :
 (result frame configuration).2.2.1 (intoActual frame configuration index)=
 updateInventory (R:=ℤ) (oldEnvironment frame configuration (occurrence frame configuration))
  (increment frame configuration (occurrence frame configuration)) (Vector.word frame configuration index) :=
 (result_coordinate frame configuration (intoActual frame configuration index)).trans
  (congrArg (updateInventory (R:=ℤ) (oldEnvironment frame configuration (occurrence frame configuration))
    (increment frame configuration (occurrence frame configuration))) (actual_word_read frame configuration index))
theorem installed_result : (queryFace frame configuration).rootRead=result frame configuration := rfl
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (queryRoot frame configuration) (visit frame configuration) (actualFrame frame configuration).currentState.U7
 (actualFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (queryRoot frame configuration) (visit frame configuration) (actualFrame frame configuration).currentState.U7
 (actualFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
theorem mother_whole : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem mother_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
abbrev nativeGenerated (stage : Nat) := (Vector.Action.nativeGenerated frame configuration stage,
 generated (Faces.Native.nativeFrame frame configuration stage) Faces.Native.R.programme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
