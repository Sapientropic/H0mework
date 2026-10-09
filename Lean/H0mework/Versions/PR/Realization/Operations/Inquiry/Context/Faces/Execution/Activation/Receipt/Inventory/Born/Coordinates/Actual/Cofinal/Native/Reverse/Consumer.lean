import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
attribute [local instance] valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage : Nat)
theorem query_recovery : (result frame configuration sourceStage stage).2.2.1=
 F.recover (runtime frame configuration sourceStage) (source frame configuration sourceStage)
  (stateAt frame configuration sourceStage stage)
  (B.reverse (runtime frame configuration sourceStage) (source frame configuration sourceStage) (stateAt frame configuration sourceStage stage)) := by
 have actual := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
  (occurrence frame configuration sourceStage stage)).trans (eval_liftExpr _ _ _)
 have pair := congrArg₂ Prod.mk (SourceOperationExecution.Coefficients.expression_eval
   (word frame configuration sourceStage stage) (SourceOperationInquiry.Context.readEnv (runtime frame configuration sourceStage)
    (source frame configuration sourceStage) (stateAt frame configuration sourceStage stage)))
  (SourceOperationExecution.Coefficients.expression_effect (word frame configuration sourceStage stage)
   (SourceOperationInquiry.Context.readEnv (runtime frame configuration sourceStage) (source frame configuration sourceStage)
    (stateAt frame configuration sourceStage stage)) (SourceOperationInquiry.Context.increment (runtime frame configuration sourceStage)
      (source frame configuration sourceStage) (stateAt frame configuration sourceStage stage)))
 exact actual.trans (pair.trans (SourceOperationInquiry.Context.Faces.Reverse.reverse_recover
  (runtime frame configuration sourceStage) (source frame configuration sourceStage) (stateAt frame configuration sourceStage stage)).symm)
theorem complete_reverse : type_of% (SourceOperationInquiry.Context.Faces.Reverse.reverse_pair
 (runtime frame configuration sourceStage) (source frame configuration sourceStage) (stateAt frame configuration sourceStage stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.reverse_pair _ _ _
theorem retained_evidence : (sourceFace frame configuration sourceStage stage).rootRead.2.2.1=
 B.retainedTarget (runtime frame configuration sourceStage) (source frame configuration sourceStage) (stateAt frame configuration sourceStage stage) := rfl
theorem actual_reader : reader frame configuration sourceStage stage (occurrence frame configuration sourceStage stage)=
 (sourceFace frame configuration sourceStage stage).rootRead.2.2.2.2 := rfl
theorem installed_result : (queryFace frame configuration sourceStage stage).rootRead=result frame configuration sourceStage stage := rfl
theorem exact_cost : (result frame configuration sourceStage stage).2.1.2.length=
 remaining (raw frame configuration sourceStage stage).expression := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem original_tick : type_of% (SourceOperationInquiry.Context.Faces.Reverse.actual_tick
 (runtime frame configuration sourceStage) (stateAt frame configuration sourceStage stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.actual_tick _ _
theorem source_ledger : (queryRoot frame configuration sourceStage stage).toAuthoritativeRoot.toLedgerRoot=
 (original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem whole_first : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem literal_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (queryRoot frame configuration sourceStage stage) (original frame configuration sourceStage stage).visit
 (original frame configuration sourceStage stage).U7 (original frame configuration sourceStage stage).calculus
 (reader frame configuration sourceStage stage)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (queryRoot frame configuration sourceStage stage) (original frame configuration sourceStage stage).visit
 (original frame configuration sourceStage stage).U7 (original frame configuration sourceStage stage).calculus
 (reader frame configuration sourceStage stage)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
abbrev nativeGenerated (nativeStage : Nat) := (Actual.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
