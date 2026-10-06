import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count iterations : Nat)
theorem actual_class : actualClass frame configuration sourceStage stage count iterations=
 SourceOperationInquiry.Context.Native.Pairing.Orbit.canonical
 (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (Finsupp.single (expression frame configuration sourceStage stage count iterations) (1:ℤ)) := O.class_source _ _ _ _
theorem paid_class_read : (result frame configuration sourceStage stage count iterations).2.2.1=
 SourceOperationInquiry.Context.Native.Pairing.Orbit.read (Future.runtime frame configuration sourceStage stage)
 (Future.source frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count)
 (actualClass frame configuration sourceStage stage count iterations) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot (reader frame configuration sourceStage stage count iterations)
  (Query.occurrence frame configuration sourceStage stage count)).trans
 ((eval_liftExpr _ _ _).trans (O.class_read (Future.runtime frame configuration sourceStage stage)
  (Future.source frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count)
  (Query.expression frame configuration sourceStage stage count) iterations).symm)
theorem complete_charge : type_of% (O.complete_charge (Future.runtime frame configuration sourceStage stage)
 (Future.source frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count)
 (Query.expression frame configuration sourceStage stage count) iterations) := O.complete_charge _ _ _ _ iterations
theorem complete_inventory (index : Fin (iterations+1)) (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (O.trace (Future.runtime frame configuration sourceStage stage)
  (Future.source frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count)
  (Query.expression frame configuration sourceStage stage count) index.val)).trace) :
 event ∈ (history frame configuration sourceStage stage count iterations).trace := O.complete_inventory _ _ _ _ iterations index event present
theorem source_class : (sourceFace frame configuration sourceStage stage count iterations).rootRead.2.1=
 actualClass frame configuration sourceStage stage count iterations := rfl
theorem history_read : (sourceFace frame configuration sourceStage stage count iterations).rootRead.2.2.2.1=
 history frame configuration sourceStage stage count iterations := rfl
theorem actual_reader : reader frame configuration sourceStage stage count iterations (Query.occurrence frame configuration sourceStage stage count)=
 (sourceFace frame configuration sourceStage stage count iterations).rootRead.2.2.2.2 := rfl
theorem installed_result : (face frame configuration sourceStage stage count iterations).rootRead=result frame configuration sourceStage stage count iterations := rfl
theorem paid_charge : (result frame configuration sourceStage stage count iterations).2.1.2.length=remaining (raw frame configuration sourceStage stage count iterations).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem source_ledger : (root frame configuration sourceStage stage count iterations).toAuthoritativeRoot.toLedgerRoot=
 (Query.original frame configuration sourceStage stage count).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem whole_first : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem literal_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (root frame configuration sourceStage stage count iterations) (Query.original frame configuration sourceStage stage count).visit
 (Query.original frame configuration sourceStage stage count).U7 (Query.original frame configuration sourceStage stage count).calculus
 (reader frame configuration sourceStage stage count iterations)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (root frame configuration sourceStage stage count iterations) (Query.original frame configuration sourceStage stage count).visit
 (Query.original frame configuration sourceStage stage count).U7 (Query.original frame configuration sourceStage stage count).calculus
 (reader frame configuration sourceStage stage count iterations)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
abbrev nativeGenerated (nativeStage : Nat) := (Coimage.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage count iterations => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage count iterations)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
