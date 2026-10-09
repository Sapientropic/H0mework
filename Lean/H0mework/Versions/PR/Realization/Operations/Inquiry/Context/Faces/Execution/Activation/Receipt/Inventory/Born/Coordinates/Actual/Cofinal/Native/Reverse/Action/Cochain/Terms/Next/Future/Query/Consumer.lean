import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count : Nat)
theorem native_pair :
 ((expression frame configuration sourceStage stage count).eval (environment frame configuration sourceStage stage count),
 (expression frame configuration sourceStage stage count).effect (environment frame configuration sourceStage stage count)
  (increment frame configuration sourceStage stage count))=
 (evaluation (R:=ℤ) (SourceOperationInquiry.Context.readEnv (Future.runtime frame configuration sourceStage stage)
   (Future.source frame configuration sourceStage stage) (state frame configuration sourceStage stage count).tick.nextState)
   (Future.word frame configuration sourceStage stage count),
 effectEvaluator (R:=ℤ) (SourceOperationInquiry.Context.readEnv (Future.runtime frame configuration sourceStage stage)
   (Future.source frame configuration sourceStage stage) (state frame configuration sourceStage stage count).tick.nextState)
   (SourceOperationInquiry.Context.increment (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
    (state frame configuration sourceStage stage count).tick.nextState) (Future.word frame configuration sourceStage stage count)) :=
 (SourceOperationInquiry.Context.Native.Orbit.literalnext_pair (Future.runtime frame configuration sourceStage stage)
  (Future.source frame configuration sourceStage stage) (Coefficients.expression (Future.word frame configuration sourceStage stage count))
  (state frame configuration sourceStage stage count)).trans
  (congrArg₂ Prod.mk (Coefficients.expression_eval _ _) (Coefficients.expression_effect _ _ _))
theorem exact_joint_field : (result frame configuration sourceStage stage count).2.2.1=
 SourceOperationInquiry.Context.Faces.Cofinal.read (Future.runtime frame configuration sourceStage stage)
 (Future.source frame configuration sourceStage stage) (count+1) 0
 (SourceOperationInquiry.Context.Faces.Cofinal.next (Future.runtime frame configuration sourceStage stage)
  (Future.source frame configuration sourceStage stage) count (Future.relationField frame configuration sourceStage stage count)) 0 := by
 have paid := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage count).toAuthoritativeRoot (reader frame configuration sourceStage stage count)
  (occurrence frame configuration sourceStage stage count)).trans
  ((eval_liftExpr _ _ _).trans (native_pair frame configuration sourceStage stage count))
 exact paid.trans (SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read
  (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage) count 0 0).symm
theorem exact_runtime_root : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_node
 (Future.initial frame configuration sourceStage stage) (Future.consumer frame configuration sourceStage stage) count) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_node _ _ count
theorem installed_word : (sourceFace frame configuration sourceStage stage count).rootRead.1=
 Future.word frame configuration sourceStage stage count := rfl
theorem installed_field : (sourceFace frame configuration sourceStage stage count).rootRead.2.1=
 Future.relationField frame configuration sourceStage stage count := rfl
theorem installed_witness : (sourceFace frame configuration sourceStage stage count).rootRead.2.2.1=
 Future.witness frame configuration sourceStage stage count := rfl
theorem actual_reader : reader frame configuration sourceStage stage count (occurrence frame configuration sourceStage stage count)=
 (sourceFace frame configuration sourceStage stage count).rootRead.2.2.2 := rfl
theorem installed_result : (queryFace frame configuration sourceStage stage count).rootRead=result frame configuration sourceStage stage count := rfl
theorem source_ledger : (queryRoot frame configuration sourceStage stage count).toAuthoritativeRoot.toLedgerRoot=
 (original frame configuration sourceStage stage count).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem paid_charge : (result frame configuration sourceStage stage count).2.1.2.length=remaining (raw frame configuration sourceStage stage count).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem whole_first : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration sourceStage stage count)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem literal_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration sourceStage stage count)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (queryRoot frame configuration sourceStage stage count) (original frame configuration sourceStage stage count).visit
 (original frame configuration sourceStage stage count).U7 (original frame configuration sourceStage stage count).calculus
 (reader frame configuration sourceStage stage count)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (queryRoot frame configuration sourceStage stage count) (original frame configuration sourceStage stage count).visit
 (original frame configuration sourceStage stage count).U7 (original frame configuration sourceStage stage count).calculus
 (reader frame configuration sourceStage stage count)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
abbrev nativeGenerated (nativeStage : Nat) := (Future.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage count => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage count)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
