import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Installation
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Tree
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Runtime

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual
namespace Receipt
export SourceGeneratedInquiryReceiptAction (actualMaterial afterEnvironment actual_query_state actual_raw actual_environment actionReader actionResultAt)
end Receipt
namespace Req
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
 (expression input relations updated_value residual_value budget)
end Req
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query query_generated resultFace actualOccurrence)
end Q
namespace L
export Lower.SourceFamily.Foresight.Paid.Ledger (SourceEvent eventWord run writeEvent run_contains)
end L
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (data:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev cfg:=Indexed.Installation.configuration binding n data.2
abbrev material:=Receipt.actualMaterial data.1 (cfg binding n data)
abbrev after:=Receipt.afterEnvironment data.1 (cfg binding n data)
abbrev actionRaw:=Receipt.actionReader data.1 (cfg binding n data) (Q.actualOccurrence data.1)
def beta:=relationMap (R:=ℤ) (material binding n data).environment
 (Req.relations (R:=ℤ) (material binding n data))
def expression:=Req.expression (material binding n data)
def event:L.SourceEvent (W:=W) (X:=X) (s:=s) n:=.generator (expression binding n data)
def sourceTree:=RootedAccountedUnfolding.zero (event binding n data)
def literalWord:=L.eventWord n (event binding n data)
def written:=L.run (L.writeEvent binding n data) (sourceTree binding n data)

theorem actual_state:(material binding n data).state=
 (Receipt.actionResultAt data.1 (cfg binding n data) (Q.actualOccurrence data.1)).2.1:=
 Receipt.actual_query_state _ _
theorem actual_raw:(material binding n data).raw=(actionRaw binding n data).expression:=rfl
theorem actual_environment:(material binding n data).environment=(actionRaw binding n data).environment:=rfl
theorem actual_increment:(material binding n data).increment=
 after binding n data-(actionRaw binding n data).environment:=
 congrArg (after binding n data-·) (actual_environment binding n data)

theorem effect_generated:(expression binding n data).eval (Req.input (material binding n data)).environment=
 effectEvaluator (R:=ℤ) (material binding n data).environment (material binding n data).increment
  (beta binding n data):=Req.updated_value (material binding n data)
theorem inverse_generated:(residualEquivRange
 (evaluation (R:=ℤ) (Req.input (material binding n data)).environment)
 (canonicalResidual (evaluation (R:=ℤ) (Req.input (material binding n data)).environment)
  (beta binding n data))).val=(expression binding n data).eval (Req.input (material binding n data)).environment:=
 Req.residual_value (material binding n data)
theorem own_request_budget:remaining (expression binding n data)=
 remaining (material binding n data).raw+remaining (material binding n data).state.1+2:=
 Req.budget (material binding n data)

theorem literal_writer_fee:
 (Lower.SourceFamily.Foresight.Paid.paidTrace binding n data s (literalWord binding n data)).length=
 remaining (Lower.SourceFamily.Foresight.Paid.expression (W:=W) (X:=X) n s (literalWord binding n data)):=
 Lower.SourceFamily.Foresight.Paid.complete_fee _ _ _ _ _

theorem source_event_present:event binding n data∈(sourceTree binding n data).trace:=List.mem_cons_self

theorem all_literal_paid (entry)
 (present:entry∈(L.writeEvent binding n data (event binding n data)).trace):
 entry∈(written binding n data).trace:=L.run_contains _ _ _ (source_event_present binding n data) _ present
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
