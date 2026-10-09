import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Factory
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Paid
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

def actualEnvironment :=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
  (Lower.SourceFamily.step (factory (s:=s) binding) n data).1
  (Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1)
   (Lower.SourceFamily.step (factory (s:=s) binding) n data).2)).raw.environment

theorem source_environment : sourceEnv binding n data=actualEnvironment binding n data :=
 environment_stock_independent binding n data.2 data.1
  (sourceScalar binding n data) (Lower.SourceFamily.scalar (factory (s:=s) binding) n data)
  (sourcePair binding n data) (Lower.SourceFamily.pair (factory (s:=s) binding) n data)

theorem actual_source_value (t : S) (word : Word (W:=W) (X:=X) n t) :
 (result binding n data t word).2.2.1=
 evaluation (R:=ℤ) (actualEnvironment binding n data) (liftMap word) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
 ((Coefficients.expression_eval _ _).trans
  (congrArg (fun environment => evaluation (R:=ℤ) environment (liftMap word))
   (source_environment binding n data)))

theorem actual_new_kernel (t : S) (word : Word (W:=W) (X:=X) n t) :
 evaluation (R:=ℤ) (actualEnvironment binding n data)
  (relationMap (R:=ℤ) (sourceEnv binding n data)
   ((paidTrace binding n data t word).relationWords (R:=ℤ)))=0 :=
 (congrArg (fun environment => evaluation (R:=ℤ) environment
  (relationMap (R:=ℤ) (sourceEnv binding n data)
   ((paidTrace binding n data t word).relationWords (R:=ℤ))))
  (source_environment binding n data).symm).trans (generated_new_kernel binding n data t word)

theorem step_environment
 (paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law data.1.registered.input.environment data.1.registered.input.expression)
  data.1.event.state) (actual : data.1.action=.inr paid) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
  (Lower.SourceFamily.step (factory (s:=s) binding) n data).1
  (Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1)
   (Lower.SourceFamily.step (factory (s:=s) binding) n data).2)).raw.environment=
 pairEnvironment (Lower.SourceFamily.Foresight.Update.after binding n data.2 data.1)
  (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+1))
   (Lower.SourceFamily.Foresight.Update.after binding n data.2 data.1)-
   Lower.SourceFamily.Foresight.Update.after binding n data.2 data.1) :=
 Lower.SourceFamily.Foresight.Update.paid_environment binding n data.2 data.1
  (Lower.SourceFamily.scalar (factory (s:=s) binding) n data)
  (Lower.SourceFamily.pair (factory (s:=s) binding) n data) paid actual

theorem tail_next (source : Lower.SourceFamily.Factory W X s)
 (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
 (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
 (language : firstCfg.LowVar=X) (k : Nat) :
 Lower.SourceFamily.tailData source initial firstCfg language (k+1)=
 Lower.SourceFamily.step source (k+1) (Lower.SourceFamily.tailData source initial firstCfg language k) := rfl
end Lower.SourceFamily.Foresight.Paid
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
