import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Future.Actual
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query)
end Q
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower (configuration)
end L
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
theorem raw_generated : (Q.query frame configuration).raw=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame configuration).reader
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) :=
 congrArg (fun query => query.raw) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated frame configuration)

variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
abbrev cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.R.programme seed

theorem source_query_charge : 2≤remaining (Q.query frame (cfg seed)).raw.expression := by
 have native := Future.native_query_charge frame seed
 rw [raw_generated] at native ⊢
 exact native
variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) (cfg seed).LowVar s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) (cfg seed).LowVar s)))
variable (nextSeed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) (cfg seed).LowVar s)))

def receiver := Future.receiver frame (cfg seed) scalar pair

theorem next_raw_environment : (Q.query (receiver frame seed scalar pair) (Continuation.R.programme nextSeed)).raw.environment=
 pairEnvironment (SourceGeneratedInquiryReceiptAction.afterEnvironment frame (cfg seed)) 0 := by
 have square := Future.actual_future_square frame (cfg seed) scalar pair nextSeed (source_query_charge frame seed)
 rw [Future.nextRaw,raw_generated] at square
 rw [raw_generated]
 exact square

end Future.Actual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
