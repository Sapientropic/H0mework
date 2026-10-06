import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch.Calls.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Iteration.Current
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch.Calls
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count iterations : Nat)
theorem observation_source (index : CallIndex frame configuration sourceStage stage count iterations) :
 observations frame configuration sourceStage stage count iterations index=
 SourceOperationInquiry.Context.readEnv (Future.runtime frame configuration sourceStage stage)
 (Future.source frame configuration sourceStage stage)
 ((Future.runtime frame configuration sourceStage stage).stateAt (count+index.val)) :=
 (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.environment_actual
  (Future.initial frame configuration sourceStage stage) (Future.consumer frame configuration sourceStage stage) (count+index.val)).symm
theorem observation_recovery : type_of% (snapshots_source
 (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage) count
 (bound frame configuration sourceStage stage count iterations)
 (observations frame configuration sourceStage stage count iterations)
 (observation_source frame configuration sourceStage stage count iterations)) :=
 snapshots_source _ _ _ _ _ (observation_source frame configuration sourceStage stage count iterations)
theorem old_source : type_of% (observation_recovery frame configuration sourceStage stage count iterations).1 :=
 (observation_recovery frame configuration sourceStage stage count iterations).1
theorem increment_source : type_of% (observation_recovery frame configuration sourceStage stage count iterations).2 :=
 (observation_recovery frame configuration sourceStage stage count iterations).2
theorem environment_source : environment frame configuration sourceStage stage count iterations=
 SourceOperationInquiry.Context.Native.Orbit.Finite.Batch.environment (sourceSeed frame configuration sourceStage stage count)
 iterations (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage) count :=
 congrArg₂ (fun old change => InventoryVector.environment (SourceOperationInquiry.Context.Native.Pairing.Orbit.Batch.Index iterations)
  (pairEnvironment old change)) (old_source frame configuration sourceStage stage count iterations)
   (increment_source frame configuration sourceStage stage count iterations)
theorem original_query : (raw frame configuration sourceStage stage count iterations).expression.eval
 (raw frame configuration sourceStage stage count iterations).environment=
 (Batch.raw frame configuration sourceStage stage count iterations).expression.eval
 (Batch.raw frame configuration sourceStage stage count iterations).environment :=
 (congrArg (fun env => (expression frame configuration sourceStage stage count iterations).eval env)
  (environment_source frame configuration sourceStage stage count iterations)).trans
  (F.original_query (sourceSeed frame configuration sourceStage stage count) iterations
   (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage) count)
theorem paid_value : (result frame configuration sourceStage stage count iterations).2.2.1=
 (Batch.result frame configuration sourceStage stage count iterations).2.2.1 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
  ((original_query frame configuration sourceStage stage count iterations).trans
   (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Batch.baseRoot frame configuration sourceStage stage count iterations).toAuthoritativeRoot
    (Batch.reader frame configuration sourceStage stage count iterations) (Query.occurrence frame configuration sourceStage stage count)).symm)
private theorem shared_written {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)] {t : T}
 (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr A X t)))
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=A) (Var:=X) (sort:=t))
 (event) (present : event ∈ (SourceOperationPaidRelations.exposure
  (Shared.resultAt frame (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.configuration seed)
   (Shared.actualOccurrence frame)).2.1.2).trace) :
 event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.completeWrittenInventory
  seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (Shared.actualOccurrence frame)).trace := by
 have same := RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame
   (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.configuration seed)).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
  (SourceOperationInquiry.Context.Faces.Execution.Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.queryReader seed
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (Shared.actualOccurrence frame))
 exact SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.complete_query_trace
  seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (Shared.actualOccurrence frame) event
  ((congrArg (fun inventory => event ∈ inventory.trace) same) ▸ present)
theorem call_written (index : CallIndex frame configuration sourceStage stage count iterations) (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (callMaterial frame configuration sourceStage stage count iterations index).2.2.1.2.1.2).trace) :
 type_of% (shared_written (Future.seed frame configuration sourceStage stage)
  (Future.frameAt frame configuration sourceStage stage (count+index.val)) event present) :=
 shared_written _ _ event present
abbrev actualCalls (index : CallIndex frame configuration sourceStage stage count iterations) :=
 (PLift.up (Future.actual_query frame configuration sourceStage stage (count+index.val)),
 PLift.up (Future.actual_answer frame configuration sourceStage stage (count+index.val)),
 PLift.up (Future.actual_next frame configuration sourceStage stage (count+index.val)))
def callCost := (List.ofFn (fun index : CallIndex frame configuration sourceStage stage count iterations =>
 remaining (callMaterial frame configuration sourceStage stage count iterations index).2.2.1.1.expression)).sum
def callCharge := (List.ofFn (fun index : CallIndex frame configuration sourceStage stage count iterations =>
 (callMaterial frame configuration sourceStage stage count iterations index).2.2.1.2.1.2.length)).sum
theorem call_charge : callCharge frame configuration sourceStage stage count iterations=
 callCost frame configuration sourceStage stage count iterations := by
 apply congrArg List.sum
 apply congrArg List.ofFn
 funext index
 exact RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
   (Future.frameAt frame configuration sourceStage stage (count+index.val)) (Future.consumer frame configuration sourceStage stage)).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
   (Future.frameAt frame configuration sourceStage stage (count+index.val)) (Future.consumer frame configuration sourceStage stage)).reader
  (Shared.actualOccurrence (Future.frameAt frame configuration sourceStage stage (count+index.val)))
def invocation (index : CallIndex frame configuration sourceStage stage count iterations) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.generatePayment
  (Future.consumer frame configuration sourceStage stage) (Future.frameAt frame configuration sourceStage stage (count+index.val))
abbrev callFrame (index : CallIndex frame configuration sourceStage stage count iterations) :=
 Future.frameAt frame configuration sourceStage stage (count+index.val)
abbrev callReader (index : CallIndex frame configuration sourceStage stage count iterations) :=
 fun (_ : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
  (callFrame frame configuration sourceStage stage count iterations index) (Future.consumer frame configuration sourceStage stage)).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit
   (callFrame frame configuration sourceStage stage count iterations index)).current) =>
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
  (callFrame frame configuration sourceStage stage count iterations index) (Future.consumer frame configuration sourceStage stage)).reader
  (Shared.actualOccurrence (callFrame frame configuration sourceStage stage count iterations index))
def callPayment (index : CallIndex frame configuration sourceStage stage count iterations)
 (step : Fin (remaining (callMaterial frame configuration sourceStage stage count iterations index).2.2.1.1.expression)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
   (callFrame frame configuration sourceStage stage count iterations index) (Future.consumer frame configuration sourceStage stage)).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit
   (callFrame frame configuration sourceStage stage count iterations index)).current
  (callReader frame configuration sourceStage stage count iterations index) step
abbrev sourceGenerated := (callMaterial frame configuration sourceStage stage count iterations,
 actualCalls frame configuration sourceStage stage count iterations,
 fun index => invocation frame configuration sourceStage stage count iterations index,
 fun index step => callPayment frame configuration sourceStage stage count iterations index step)
theorem actual_reader : reader frame configuration sourceStage stage count iterations (Query.occurrence frame configuration sourceStage stage count)=
 (sourceFace frame configuration sourceStage stage count iterations).rootRead.2.2 := rfl
theorem installed_result : (face frame configuration sourceStage stage count iterations).rootRead=result frame configuration sourceStage stage count iterations := rfl
theorem paid_charge : (result frame configuration sourceStage stage count iterations).2.1.2.length=
 SourceOperationInquiry.Context.Native.Pairing.Orbit.totalCost (sourceSeed frame configuration sourceStage stage count) iterations+2*(iterations+1) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
 (SourceOperationInquiry.Context.Native.Pairing.Orbit.Batch.query_charge _ _)
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
 sourceGenerated frame configuration sourceStage stage count iterations,
 fun step => payment frame configuration sourceStage stage count iterations step,
 writtenGenerated frame configuration sourceStage stage count iterations)
abbrev nativeGenerated (nativeStage : Nat) := (Batch.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage count iterations => paidGenerated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage count iterations)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Batch.Calls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
