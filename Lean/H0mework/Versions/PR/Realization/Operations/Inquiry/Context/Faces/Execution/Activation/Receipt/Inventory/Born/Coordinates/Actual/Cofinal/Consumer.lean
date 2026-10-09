import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (stage : Nat)
theorem complete_word : type_of% (SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback
 (runtime frame configuration) (source frame configuration) stage) :=
 SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback _ _ _
theorem complete_future_zero : type_of% (SourceOperationInquiry.Context.Faces.Cofinal.relation_zero_iff
 (runtime frame configuration) (source frame configuration) stage) :=
 SourceOperationInquiry.Context.Faces.Cofinal.relation_zero_iff _ _ _
theorem successor_read (bound : Nat) (index : Fin (bound+1)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read
  (runtime frame configuration) (source frame configuration) stage bound index) :=
 SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read _ _ _ _ _
theorem native_pair :
 ((expression frame configuration stage).eval (environment frame configuration stage),
  (expression frame configuration stage).effect (environment frame configuration stage) (increment frame configuration stage))=
 (evaluation (R:=ℤ) (SourceOperationInquiry.Context.readEnv (runtime frame configuration) (source frame configuration)
   (stateAt frame configuration stage).tick.nextState) (relationWord frame configuration stage),
  effectEvaluator (R:=ℤ) (SourceOperationInquiry.Context.readEnv (runtime frame configuration) (source frame configuration)
   (stateAt frame configuration stage).tick.nextState)
   (SourceOperationInquiry.Context.increment (runtime frame configuration) (source frame configuration)
    (stateAt frame configuration stage).tick.nextState) (relationWord frame configuration stage)) :=
 (SourceOperationInquiry.Context.Native.Orbit.literalnext_pair (runtime frame configuration) (source frame configuration)
  (SourceOperationExecution.Coefficients.expression (relationWord frame configuration stage)) (stateAt frame configuration stage)).trans
  (congrArg₂ Prod.mk (SourceOperationExecution.Coefficients.expression_eval _ _)
   (SourceOperationExecution.Coefficients.expression_effect _ _ _))
theorem query_successor_field : (result frame configuration stage).2.2.1=
 SourceOperationInquiry.Context.Faces.Cofinal.read (runtime frame configuration) (source frame configuration) (stage+1) 0
  (C.next (runtime frame configuration) (source frame configuration) stage (field frame configuration stage)) 0 := by
 have pair := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration stage).toAuthoritativeRoot (reader frame configuration stage) (occurrence frame configuration stage)).trans
  ((eval_liftExpr _ _ _).trans (native_pair frame configuration stage))
 have read := SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read
  (runtime frame configuration) (source frame configuration) stage 0 0
 exact pair.trans read.symm
theorem installed_query : (queryFace frame configuration stage).rootRead=result frame configuration stage := rfl
theorem installed_word : (sourceFace frame configuration stage).rootRead.1=relationWord frame configuration stage := rfl
theorem installed_field : (sourceFace frame configuration stage).rootRead.2.1=field frame configuration stage := rfl
theorem installed_witness : (sourceFace frame configuration stage).rootRead.2.2.1=witness frame configuration stage := rfl
theorem actual_reader : reader frame configuration stage (occurrence frame configuration stage)=
 (sourceFace frame configuration stage).rootRead.2.2.2 := rfl
theorem source_ledger : (queryRoot frame configuration stage).toAuthoritativeRoot.toLedgerRoot=
 (original frame configuration stage).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem paid_cost : (result frame configuration stage).2.1.2.length=remaining (raw frame configuration stage).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem whole_first : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem literal_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (queryRoot frame configuration stage) (original frame configuration stage).visit (original frame configuration stage).U7
 (original frame configuration stage).calculus (reader frame configuration stage)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (queryRoot frame configuration stage) (original frame configuration stage).visit (original frame configuration stage).U7
 (original frame configuration stage).calculus (reader frame configuration stage)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
abbrev nativeGenerated (nativeStage : Nat) :=
 (Actual.nativeGenerated frame configuration nativeStage,
  fun stage => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
