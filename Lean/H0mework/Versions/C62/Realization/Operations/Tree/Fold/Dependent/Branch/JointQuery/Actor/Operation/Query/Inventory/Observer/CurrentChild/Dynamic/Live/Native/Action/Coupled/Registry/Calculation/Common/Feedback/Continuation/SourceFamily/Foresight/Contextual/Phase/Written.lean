import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Written
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Phase
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
def requestWord := Paid.Ledger.eventWord n (phaseEvent binding n data)
abbrev requestExpression := Paid.expression (W:=W) (X:=X) n s (requestWord binding n data)
abbrev requestTrace := Paid.paidTrace binding n data s (requestWord binding n data)
abbrev requestWritten := Paid.writtenAt binding n data (requestWord binding n data)

theorem generated_input_in_stock :
 PresentedRelationEventAt.generator (requestExpression binding n data) ∈ (Written.stock binding n data).trace :=
 Written.paid_in_stock binding n data (phaseEvent binding n data) (phase_source_present binding n data)
  _ List.mem_cons_self

theorem complete_paid_in_stock (event) (present : event ∈ (requestWritten binding n data).trace) :
 event ∈ (Written.stock binding n data).trace :=
 Written.paid_in_stock binding n data (phaseEvent binding n data) (phase_source_present binding n data) event present

theorem complete_paid_in_history (event) (present : event ∈ (requestWritten binding n data).trace) :
 event ∈ ((Written.jointHistory binding n data).observation 0).trace :=
 Written.paid_in_history binding n data (phaseEvent binding n data) (phase_source_present binding n data) event present

theorem complete_paid_in_next_written (event) (present : event ∈ (requestWritten binding n data).trace) :
 event ∈ (Written.jointWritten binding n data).trace :=
 Written.paid_in_complete_written binding n data (phaseEvent binding n data) (phase_source_present binding n data) event present

theorem literal_next_inventory : (Written.receiver binding n data).pairInventory=some (Written.stock binding n data) :=
 Written.receiver_pair binding n data

theorem native_next_consumes : type_of% (Written.native_query_joint_expression binding n data) :=
 Written.native_query_joint_expression binding n data

theorem full_source_charge : (requestTrace binding n data).length=remaining (requestExpression binding n data) :=
 Paid.complete_fee binding n data s (requestWord binding n data)

theorem all_step_relations :
 (SourceOperationPaidRelations.words (requestTrace binding n data)).length=(requestTrace binding n data).length :=
 Paid.all_paid_relations binding n data s (requestWord binding n data)
end Lower.SourceFamily.Foresight.Contextual.Phase
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end

