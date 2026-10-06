import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Iteration.Current
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count iterations : Nat)
private theorem evaluated_coordinate {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)] {t : T}
 {p : SourceNativeInquiryEngineProcess.{u}} (r : SourceNativeInquiryRuntime p)
 (input : SourceOperationInquiry.Context.RawSource (PhysicalValue:=A) (PhysicalVar:=X) (sort:=t) r) (state : r.State)
 (seed : Expr A (SourceOperationInquiry.Context.Native.Orbit.Var X) t) (n : Nat)
 (index : B.Index n) (values : B.Index n → PairValue A t)
 (generated : values=(B.query seed n).eval (B.environment n r input state)) :
 values index=((SourceOperationInquiry.Context.Native.Pairing.Orbit.iterate seed index.val).eval
   (SourceOperationInquiry.Context.Native.Pairing.Orbit.old r input state),
  (SourceOperationInquiry.Context.Native.Pairing.Orbit.iterate seed index.val).effect
   (SourceOperationInquiry.Context.Native.Pairing.Orbit.old r input state)
   (SourceOperationInquiry.Context.Native.Pairing.Orbit.increment r input state)) :=
 (congrFun generated index).trans (B.coordinate seed n r input state index)
theorem paid_coordinate (index : B.Index iterations) : type_of% (evaluated_coordinate
 (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (Query.state frame configuration sourceStage stage count) (sourceSeed frame configuration sourceStage stage count) iterations index
 (result frame configuration sourceStage stage count iterations).2.2.1
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot
  (reader frame configuration sourceStage stage count iterations) (Query.occurrence frame configuration sourceStage stage count))) :=
 evaluated_coordinate _ _ _ _ _ index _ (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _)
theorem paid_class (index : B.Index iterations) :
 (result frame configuration sourceStage stage count iterations).2.2.1 index=
 SourceOperationInquiry.Context.Native.Pairing.Orbit.read (Future.runtime frame configuration sourceStage stage)
  (Future.source frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count)
  (SourceOperationInquiry.Context.Native.Pairing.Orbit.actedClass (Future.runtime frame configuration sourceStage stage)
    (Future.source frame configuration sourceStage stage) (sourceSeed frame configuration sourceStage stage count) index.val) :=
 (paid_coordinate frame configuration sourceStage stage count iterations index).trans
 (SourceOperationInquiry.Context.Native.Pairing.Orbit.class_read (Future.runtime frame configuration sourceStage stage)
  (Future.source frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count)
  (sourceSeed frame configuration sourceStage stage count) index.val).symm
private theorem read_current {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)] {t : T}
 {p : SourceNativeInquiryEngineProcess.{u}} (r : SourceNativeInquiryRuntime p)
 (input : SourceOperationInquiry.Context.RawSource (PhysicalValue:=A) (PhysicalVar:=X) (sort:=t) r)
 (seed : Expr A (SourceOperationInquiry.Context.Native.Orbit.Var X) t) (depth n : Nat)
 (index : B.Index n) (values : B.Index n → PairValue A t)
 (generated : values index=((SourceOperationInquiry.Context.Native.Pairing.Orbit.iterate seed index.val).eval
   (SourceOperationInquiry.Context.Native.Pairing.Orbit.old r input (r.stateAt depth)),
  (SourceOperationInquiry.Context.Native.Pairing.Orbit.iterate seed index.val).effect
   (SourceOperationInquiry.Context.Native.Pairing.Orbit.old r input (r.stateAt depth))
   (SourceOperationInquiry.Context.Native.Pairing.Orbit.increment r input (r.stateAt depth)))) :
 values index=(seed.eval (SourceOperationInquiry.Context.Native.Pairing.Orbit.old r input (r.stateAt (depth+index.val))),
  seed.effect (SourceOperationInquiry.Context.Native.Pairing.Orbit.old r input (r.stateAt (depth+index.val)))
   (SourceOperationInquiry.Context.Native.Pairing.Orbit.increment r input (r.stateAt (depth+index.val)))) :=
 generated.trans (SourceOperationInquiry.Context.Native.Pairing.Orbit.iterate_current r input seed depth index.val)
theorem paid_current (index : B.Index iterations) : type_of% (read_current
 (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (sourceSeed frame configuration sourceStage stage count) count iterations index
 (result frame configuration sourceStage stage count iterations).2.2.1
 (paid_coordinate frame configuration sourceStage stage count iterations index)) :=
 read_current _ _ _ _ _ index _ (paid_coordinate frame configuration sourceStage stage count iterations index)
theorem source_charge : (trace frame configuration sourceStage stage count iterations).length=
 SourceOperationInquiry.Context.Native.Pairing.Orbit.totalCost (sourceSeed frame configuration sourceStage stage count) iterations+2*(iterations+1) :=
 B.complete_charge _ _ _ _ _
theorem actual_reader : reader frame configuration sourceStage stage count iterations (Query.occurrence frame configuration sourceStage stage count)=
 (sourceFace frame configuration sourceStage stage count iterations).rootRead.2.2 := rfl
theorem installed_result : (face frame configuration sourceStage stage count iterations).rootRead=result frame configuration sourceStage stage count iterations := rfl
theorem paid_charge : (result frame configuration sourceStage stage count iterations).2.1.2.length=
 SourceOperationInquiry.Context.Native.Pairing.Orbit.totalCost (sourceSeed frame configuration sourceStage stage count) iterations+2*(iterations+1) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
 (B.query_charge _ _)
abbrev paymentReader := fun (_ : (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
 (Query.original frame configuration sourceStage stage count).visit.current) =>
 reader frame configuration sourceStage stage count iterations (Query.occurrence frame configuration sourceStage stage count)
def payment (step : Fin (remaining (raw frame configuration sourceStage stage count iterations).expression)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment
 (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot
 (Query.original frame configuration sourceStage stage count).visit.current (paymentReader frame configuration sourceStage stage count iterations) step
def sameDebt (step : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.lineage
 (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot
 (Query.original frame configuration sourceStage stage count).visit.current (paymentReader frame configuration sourceStage stage count iterations) step) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Payment.lineage _ _ _ step
theorem endpoint_no_paid : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.endpoint_no_paid
 (baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot
 (Query.original frame configuration sourceStage stage count).visit.current (paymentReader frame configuration sourceStage stage count iterations)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Payment.endpoint_no_paid _ _ _
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
abbrev writtenExposure := SourceOperationPaidRelations.exposure (result frame configuration sourceStage stage count iterations).2.1.2
def writtenFrame := {queryFrame frame configuration sourceStage stage count iterations with
 inventory:=some (writtenExposure frame configuration sourceStage stage count iterations)}
abbrev writtenInventory := Inventory.Born.inventory (writtenFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
theorem written_born (event) (present : event ∈ (writtenExposure frame configuration sourceStage stage count iterations).trace) :
 Inventory.Born.migratedEvent (writtenFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent event) ∈
 (writtenInventory frame configuration sourceStage stage count iterations).trace := by
 apply Inventory.Born.physical_event
 rw [Inventory.Born.original_physical_inventory]
 exact Inventory.Carried.input_carried_written _ _ rfl event present
theorem written_cofinal (event) (present : event ∈ (writtenExposure frame configuration sourceStage stage count iterations).trace) :
 Inventory.Born.migratedEvent (writtenFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent event) ∈
 (Inventory.Born.Coordinates.combined (writtenFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme).trace :=
 Inventory.Born.cofinal_input _ _ _ (written_born frame configuration sourceStage stage count iterations event present)
abbrev writtenGenerated := Inventory.Born.Coordinates.Actual.generated
 (writtenFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev paidGenerated := (generated frame configuration sourceStage stage count iterations,
 fun step => payment frame configuration sourceStage stage count iterations step,
 writtenGenerated frame configuration sourceStage stage count iterations)
abbrev nativeGenerated (nativeStage : Nat) := (Consumption.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage count iterations => paidGenerated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage count iterations)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
