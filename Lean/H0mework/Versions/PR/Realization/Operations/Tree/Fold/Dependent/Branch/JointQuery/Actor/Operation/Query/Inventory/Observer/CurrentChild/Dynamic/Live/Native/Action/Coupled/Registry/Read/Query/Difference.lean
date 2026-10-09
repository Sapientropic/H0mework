import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift
namespace Lower
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {W X : S → Type u} [∀ slot, AddCommGroup (W slot)] {s : S}
variable (first second : SourceOperationInquiry.Context.Raw (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
def deltaWord : Formal ℤ W X s := Finsupp.single second.expression 1-Finsupp.single first.expression 1
def deltaExpression : Expr W X s := SourceOperationInquiry.Context.Faces.Execution.expression (deltaWord first second)
def deltaRaw : SourceOperationInquiry.Context.Raw (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s) :=
 ⟨second.environment,deltaExpression first second⟩
theorem delta_eval : (deltaRaw first second).expression.eval (deltaRaw first second).environment=
 second.expression.eval second.environment-first.expression.eval second.environment := by
 rw [deltaRaw,deltaExpression,SourceOperationInquiry.Context.Faces.Execution.expression_eval]
 simp only [deltaWord,map_sub,evaluation,Finsupp.linearCombination_single,one_smul]
theorem moving_eval : second.expression.eval second.environment-first.expression.eval first.environment=
 first.expression.effect first.environment (second.environment-first.environment)+
 (deltaRaw first second).expression.eval (deltaRaw first second).environment := by
 rw [delta_eval]
 have effect := Expr.eval_update first.expression first.environment (second.environment-first.environment)
 rw [add_sub_cancel] at effect
 rw [effect]
 abel
theorem moving_paid (firstValue secondValue : W s)
 (firstPaid : firstValue=first.expression.eval first.environment)
 (secondPaid : secondValue=second.expression.eval second.environment) :
 secondValue-firstValue=first.expression.effect first.environment (second.environment-first.environment)+
 (deltaRaw first second).expression.eval (deltaRaw first second).environment := by
 rw [firstPaid,secondPaid]
 exact moving_eval first second
end Lower
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Read.Germ
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
