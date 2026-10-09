import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Written
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Effect
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Whole.Equation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Forecast
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

theorem native_actual_index (depth : data.1.depth=0) : nativeIndex n data=actualIndex n data.1 :=
 (Lower.SourceFamily.Foresight.Installed.native_actual_index n data.1 depth).symm

theorem actual_raw_source (depth : data.1.depth=0) : sourceRaw binding n data=
 (Installed.stockCoreFace binding n data.2 data.1).rootRead.1.2.2.2.2.2.2.2.1 :=by
 rw [Installed.core_material]
 exact congrArg (fun index => Reader.Core.raw binding n data.2 (nativeFrame n data) index)
  (native_actual_index n data depth)

theorem actual_source_environment (depth : data.1.depth=0) : (sourceRaw binding n data).environment=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query data.1
  (Lower.SourceFamily.cfg (factory (s:=s) binding) n data.2)).raw.environment :=
 (congrArg (fun index => (Reader.Core.raw binding n data.2 (nativeFrame n data) index).environment)
   (native_actual_index n data depth)).trans
 ((Reader.Core.raw_environment binding n data.2 (nativeFrame n data) (actualIndex n data.1)).trans
  (factory_environment binding n data.2 data.1).symm)

theorem writer_source_value : type_of% (Effect.actual_paid_value binding n data s (requestWord binding n data)) :=
 Effect.actual_paid_value _ _ _ _ _

theorem writer_full_action : type_of% ((Effect.actual_paid_value binding n data s (requestWord binding n data)).trans
 (Effect.actual_word binding n data s (requestWord binding n data))) :=
 (Effect.actual_paid_value binding n data s (requestWord binding n data)).trans
 (Effect.actual_word binding n data s (requestWord binding n data))

theorem next_query_value : type_of% (Effect.joint_paid_value binding n data (requestWord binding n data)) :=
 Effect.joint_paid_value _ _ _ _

theorem writer_new_kernel : type_of% (Effect.joint_new_kernel binding n data (requestWord binding n data)) :=
 Effect.joint_new_kernel _ _ _ _

theorem actual_next_high : type_of% (Lower.SourceFamily.Foresight.Whole.actual_high_head binding n data s
 (requestWord binding n data)) := Lower.SourceFamily.Foresight.Whole.actual_high_head _ _ _ _ _
end Lower.SourceFamily.Foresight.Contextual.Forecast
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
