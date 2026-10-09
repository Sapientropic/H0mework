import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow
open SourceOperationEffects SourceOperationExecution
variable {S : Type u} {A X : S → Type u} [∀ slot, AddCommGroup (A slot)]
variable {slot : S} (term : Expr A X slot) (firstEnvironment secondEnvironment : Env A X)
theorem left_value : (left term).eval (environment firstEnvironment secondEnvironment)=term.eval firstEnvironment :=
 term.eval_subst leftBinding (environment firstEnvironment secondEnvironment)
theorem right_value : (right term).eval (environment firstEnvironment secondEnvironment)=term.eval secondEnvironment :=
 term.eval_subst rightBinding (environment firstEnvironment secondEnvironment)
theorem left_charge : remaining (left term)=remaining term := by
 induction term with
 | var => rfl
 | const => rfl
 | add first second firstIH secondIH => exact congrArg₂ (fun a b : Nat => a+b+1) firstIH secondIH
 | linear operation argument previous => exact congrArg (fun a : Nat => a+1) previous
 | bilinear operation first second firstIH secondIH => exact congrArg₂ (fun a b : Nat => a+b+1) firstIH secondIH
theorem right_charge : remaining (right term)=remaining term := by
 induction term with
 | var => rfl
 | const => rfl
 | add first second firstIH secondIH => exact congrArg₂ (fun a b : Nat => a+b+1) firstIH secondIH
 | linear operation argument previous => exact congrArg (fun a : Nat => a+1) previous
 | bilinear operation first second firstIH secondIH => exact congrArg₂ (fun a b : Nat => a+b+1) firstIH secondIH
theorem source_value (first second : Expr A X slot) :
 (raw firstEnvironment secondEnvironment first second).expression.eval
  (raw firstEnvironment secondEnvironment first second).environment =
 first.eval firstEnvironment+second.eval secondEnvironment := by
 change (left first).eval (environment firstEnvironment secondEnvironment) +
  (right second).eval (environment firstEnvironment secondEnvironment) = _
 rw [left_value,right_value]
theorem source_charge (first second : Expr A X slot) :
 remaining (raw firstEnvironment secondEnvironment first second).expression=remaining first+remaining second+1 := by
 change remaining (left first)+remaining (right second)+1=_
 rw [left_charge,right_charge]
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
