import H0mework.Realization.Operations.Substitution.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Query.Difference
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Acted
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ.Lower
 (deltaRaw delta_eval)
end D
namespace Laws
variable {S : Type u} {W X : S → Type u} [∀ slot, AddCommGroup (W slot)] {s : S}
variable (raw : SourceOperationInquiry.Context.Raw (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (binding : ∀ slot, X slot → Expr W X slot)
def acted : SourceOperationInquiry.Context.Raw (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s) :=
 ⟨raw.environment,raw.expression.subst binding⟩
theorem delta_effect : (D.deltaRaw raw (acted raw binding)).expression.eval raw.environment=
 raw.expression.effect raw.environment (SourceSubstitution.sourceEnvironment binding raw.environment-raw.environment) := by
 change (D.deltaRaw raw (acted raw binding)).expression.eval (D.deltaRaw raw (acted raw binding)).environment=_
 rw [D.delta_eval]
 change (raw.expression.subst binding).eval raw.environment-raw.expression.eval raw.environment=_
 rw [Expr.eval_subst]
 have updated := Expr.eval_update raw.expression raw.environment
  (SourceSubstitution.sourceEnvironment binding raw.environment-raw.environment)
 rw [add_sub_cancel] at updated
 change raw.expression.eval (SourceSubstitution.sourceEnvironment binding raw.environment)=_ at updated
 change raw.expression.eval (SourceSubstitution.sourceEnvironment binding raw.environment)-raw.expression.eval raw.environment=_
 rw [updated]
 abel
end Laws
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Acted
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
