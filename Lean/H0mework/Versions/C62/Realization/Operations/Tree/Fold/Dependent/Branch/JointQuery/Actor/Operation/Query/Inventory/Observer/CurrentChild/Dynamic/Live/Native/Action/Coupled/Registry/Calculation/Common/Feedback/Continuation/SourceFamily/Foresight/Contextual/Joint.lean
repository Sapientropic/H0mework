import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Generated
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Inquiry
namespace G
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated (queryReader queryResult completeWrittenInventory query_environment complete_preserves complete_paid_trace)
end G
namespace A
export Lower.SourceFamily.Foresight.Contextual (request Req.input request_environment)
end A
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
variable (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
def rawAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue (Lower.Value W n)) (Var:=X) (sort:=s) :=
  let input := Lower.SourceFamily.Foresight.Contextual.Req.input (A.request binding n seed frame ⟨current,supplied⟩)
  ⟨input.environment,input.expression⟩
variable (index : Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
def query := G.queryReader seed frame (rawAt binding n seed frame) index.2
def written := G.completeWrittenInventory seed frame index.2 (rawAt binding n seed frame)

theorem source_query_environment : (query binding n seed frame index).environment =
    Future.Replay.Source.pairEnvironment (Future.Replay.Binding.at binding n) frame index.2 :=
  (G.query_environment seed frame index.2 (rawAt binding n seed frame index.2) _).trans
    (A.request_environment binding n seed frame index)

theorem source_complete_preserves :
    ∀ event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory seed frame index.2).trace,
      event ∈ (written binding n seed frame index).trace :=
  G.complete_preserves seed frame index.2 (rawAt binding n seed frame)

theorem source_complete_paid_trace :
    ∀ event ∈ (SourceOperationPaidRelations.exposure
      (G.queryResult seed frame index.2 (rawAt binding n seed frame)).2.1.2).trace,
      event ∈ (written binding n seed frame index).trace :=
  G.complete_paid_trace seed frame index.2 (rawAt binding n seed frame)
end Lower.SourceFamily.Foresight.Contextual.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
