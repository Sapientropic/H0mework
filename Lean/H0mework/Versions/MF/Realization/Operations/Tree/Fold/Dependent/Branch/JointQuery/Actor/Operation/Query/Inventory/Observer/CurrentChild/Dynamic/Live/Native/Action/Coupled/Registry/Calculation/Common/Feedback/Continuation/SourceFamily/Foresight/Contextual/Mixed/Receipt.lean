import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Faces
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Mixed.Effect
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Producer.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Mixed
namespace I
export Lower.SourceFamily.Foresight.Contextual.Installed (configuration actual_raw actual_trace actual_exposure face)
end I
namespace A
export SourceGeneratedInquiryReceiptAction (registered actualMaterial afterEnvironment source_effect source_inverse literal_next)
end A
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (result_effect actual_residual)
end P
variable {S : Type u} {W X : S → Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
abbrev actualIndex := Lower.SourceFamily.Foresight.Contextual.actualIndex n frame

theorem actual_result_effect : type_of% (source_result_effect binding n seed
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame)) :=
 P.result_effect _ _ _ _ _

theorem actual_result_residual : type_of% (actual_next_residual binding n seed
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame)) :=
 P.actual_residual _ _ _ _ _

theorem actual_ordered_effect : type_of% (complete_ordered_effect binding n seed
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame)) :=
 complete_ordered_effect _ _ _ _ _

theorem registered_source_expression : (A.registered frame (I.configuration binding n seed)).input.expression=
 Expr.add (Reader.expression binding n seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (actualIndex n frame))
  (Expr.linear (-AddMonoidHom.id _) (A.actualMaterial frame (I.configuration binding n seed)).state.1) := rfl

theorem registered_source_environment : (A.registered frame (I.configuration binding n seed)).input.environment=
 A.afterEnvironment frame (I.configuration binding n seed) :=
 SourceGeneratedInquiryReceiptAction.actual_updated_environment _ _

theorem registered_source_effect : type_of% (A.source_effect frame (I.configuration binding n seed)) :=
 A.source_effect _ _
theorem registered_source_residual : type_of% (A.source_inverse frame (I.configuration binding n seed)) :=
 A.source_inverse _ _
theorem registered_source_next : type_of% (A.literal_next frame (I.configuration binding n seed)) :=
 A.literal_next _ _
end Lower.SourceFamily.Foresight.Contextual.Mixed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
