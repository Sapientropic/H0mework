import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Vector.Action.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
variable (supplied : C.Occurrence (bornFrame frame configuration) (current:=current))
theorem source_expression (index : Index frame configuration) : expression frame configuration supplied index=
 (SourceOperationExecution.Coefficients.expression (word frame configuration index)).subst (binding frame configuration supplied) := rfl
theorem expression_value (index : Index frame configuration) :
 (expression frame configuration supplied index).eval (oldEnvironment frame configuration supplied)=
 evaluation (R:=ℤ) (physical frame configuration supplied).nextRaw.environment (word frame configuration index) :=
 (Expr.eval_subst _ _ _).trans (SourceOperationExecution.Coefficients.expression_eval _ _)
theorem expression_effect (index : Index frame configuration) :
 (expression frame configuration supplied index).effect (oldEnvironment frame configuration supplied) (increment frame configuration supplied)=0 :=
 (Expr.effect_subst _ _ _ _).trans (Expr.effect_zero _ _)
theorem raw_coordinate (index : Index frame configuration) :
 (raw frame configuration supplied).expression.eval (raw frame configuration supplied).environment index=
 (evaluation (R:=ℤ) (physical frame configuration supplied).nextRaw.environment (word frame configuration index),0) := by
 have read := V.query_read (Index frame configuration) (items frame configuration supplied)
  (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) index
 have single : ((items frame configuration supplied).map (fun item => if index=item.1 then
   item.2.eval (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) else 0)).sum=
  (liftExpr (expression frame configuration supplied index)).eval
   (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) := by
  simp only [items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_ite_eq (s:=Finset.univ) index
   (fun coordinate : Index frame configuration => (liftExpr (expression frame configuration supplied coordinate)).eval
     (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)))
   |>.trans (if_pos (Finset.mem_univ index))
 exact read.trans (single.trans ((eval_liftExpr _ _ _).trans
  (congrArg₂ Prod.mk (expression_value frame configuration supplied index) (expression_effect frame configuration supplied index))))
theorem actual_query : (reader frame configuration (occurrence frame configuration))=
 (actionFace frame configuration).rootRead.2.2.2.2 := rfl
theorem result_coordinate (index : Index frame configuration) :
 (result frame configuration).2.2.1 index=
 (evaluation (R:=ℤ) (physical frame configuration (occurrence frame configuration)).nextRaw.environment (word frame configuration index),0) :=
 congrFun (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (root frame configuration).toAuthoritativeRoot (reader frame configuration) (occurrence frame configuration)) index
  |>.trans (raw_coordinate frame configuration (occurrence frame configuration) index)
theorem next_inverse_read (index : Index frame configuration) :
 ((result frame configuration).2.2.1 index).1=
 (residualEquivRange (Fibre.next frame configuration (occurrence frame configuration))
  (Fibre.nextInverse frame configuration (occurrence frame configuration))).val index := by
 have previous := congrFun (Fibre.next_inverse_read frame configuration) index
 exact (congrArg Prod.fst (result_coordinate frame configuration index)).trans
  ((Vector.next_coordinate frame configuration index).symm.trans previous.symm)
theorem installed_result : (queryFace frame configuration).rootRead=result frame configuration := rfl
theorem exact_cost : (result frame configuration).2.1.2.length=
 SaturationMonoid.SourceOperationExecution.InventoryVector.charge (Index frame configuration)
  (items frame configuration (occurrence frame configuration)) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans (V.query_charge _ _)
theorem source_ledger : (queryRoot frame configuration).toAuthoritativeRoot.toLedgerRoot=
 (sourceRoot frame configuration).toAuthoritativeRoot.toLedgerRoot := rfl
theorem joint_preserved : (actionFace frame configuration).rootRead.1.2.2.2.2.1=
 Fibre.inverse frame configuration (occurrence frame configuration) := rfl
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (queryRoot frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (queryRoot frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus (reader frame configuration)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
theorem mother_whole : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem mother_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem runtime_next (stage : Nat) : type_of% (SourceGeneratedInquiryReceiptAction.runtime_next (queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme stage) := SourceGeneratedInquiryReceiptAction.runtime_next _ _ stage
abbrev nativeGenerated (stage : Nat) := (Born.nativeGenerated frame configuration stage,
 generated (Faces.Native.nativeFrame frame configuration stage) Faces.Native.R.programme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
