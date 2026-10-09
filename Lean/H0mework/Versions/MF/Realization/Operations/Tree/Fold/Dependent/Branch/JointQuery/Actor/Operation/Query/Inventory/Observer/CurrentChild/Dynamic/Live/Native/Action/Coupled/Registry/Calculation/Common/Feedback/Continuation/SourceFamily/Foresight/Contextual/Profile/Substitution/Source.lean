import H0mework.Realization.Operations.InventoryLift.Substitution
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Producer
set_option autoImplicit false
noncomputable section
universe r u v w w'
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarRelations
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Substitution
variable {S : Type u} {W X : S→Type u} [∀ t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t→Expr W X t) (n:Nat)
theorem actual_binding : Lower.SourceFamily.Foresight.Contextual.Profile.Producer.actionBinding binding (n+1)=
 (fun t name=>liftExpr (Lower.SourceFamily.Foresight.Contextual.Profile.Producer.actionBinding binding n t name)) :=rfl
theorem expression (term : Expr (Lower.Value W (n+1)) X s) :
 liftExpr (term.subst (Lower.SourceFamily.Foresight.Contextual.Profile.Producer.actionBinding binding n))=
 (liftExpr term).subst (Lower.SourceFamily.Foresight.Contextual.Profile.Producer.actionBinding binding (n+1)) :=
 SubstitutionLift.expression _ term
theorem word :
 (liftMap (R:=ℤ) (s:=s)).comp
  (substitution (R:=ℤ) (Lower.SourceFamily.Foresight.Contextual.Profile.Producer.actionBinding binding n))=
 (substitution (R:=ℤ) (Lower.SourceFamily.Foresight.Contextual.Profile.Producer.actionBinding binding (n+1))).comp liftMap :=
 SubstitutionLift.word _
end Lower.SourceFamily.Foresight.Contextual.Profile.Substitution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
