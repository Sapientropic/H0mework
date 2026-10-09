import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count : Nat)
theorem source_action : type_of% (P.actual_next (Future.runtime frame configuration sourceStage stage)
 (Future.source frame configuration sourceStage stage) (Future.word frame configuration sourceStage stage count)
 (Query.state frame configuration sourceStage stage count)) := P.actual_next _ _ _ _
theorem complete_pair : (Query.result frame configuration sourceStage stage count).2.2.1=pairedValue frame configuration sourceStage stage count := by
 have actual := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (Query.baseRoot frame configuration sourceStage stage count).toAuthoritativeRoot (Query.reader frame configuration sourceStage stage count)
  (Query.occurrence frame configuration sourceStage stage count)).trans
  ((eval_liftExpr _ _ _).trans (Query.native_pair frame configuration sourceStage stage count))
 have field := P.field_point (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
  (Future.word frame configuration sourceStage stage count) (Query.state frame configuration sourceStage stage count).tick.nextState
 have next := congrArg (P.fieldRead (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
  (Future.word frame configuration sourceStage stage count)) (SourceOperationInquiry.field_action
   (Future.runtime frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count))
 exact actual.trans (field.symm.trans next.symm)
theorem cofinal_side (bound : Nat) (index : Fin (bound+1)) : type_of% (P.cofinal_read
 (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (Future.word frame configuration sourceStage stage count) count bound index) := P.cofinal_read _ _ _ count bound index
theorem installed_pair : (face frame configuration sourceStage stage count).rootRead.2=pairedValue frame configuration sourceStage stage count := rfl
theorem same_query : (face frame configuration sourceStage stage count).rootRead.1=Query.material frame configuration sourceStage stage count := rfl
theorem same_ledger : (root frame configuration sourceStage stage count).toAuthoritativeRoot.toLedgerRoot=
 (Query.queryRoot frame configuration sourceStage stage count).toAuthoritativeRoot.toLedgerRoot := rfl
theorem whole_first : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration sourceStage stage count)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem literal_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration sourceStage stage count)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (root frame configuration sourceStage stage count) (Query.original frame configuration sourceStage stage count).visit
 (Query.original frame configuration sourceStage stage count).U7 (Query.original frame configuration sourceStage stage count).calculus
 (Query.reader frame configuration sourceStage stage count)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (root frame configuration sourceStage stage count) (Query.original frame configuration sourceStage stage count).visit
 (Query.original frame configuration sourceStage stage count).U7 (Query.original frame configuration sourceStage stage count).calculus
 (Query.reader frame configuration sourceStage stage count)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
abbrev nativeGenerated (nativeStage : Nat) := (Query.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage count => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage count)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
