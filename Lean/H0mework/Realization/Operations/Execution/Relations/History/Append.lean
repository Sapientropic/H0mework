import H0mework.Realization.Operations.Execution.Relations.History.Laws
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
variable {Sorts : Type u} {Value Var : Sorts → Type u}
variable [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {before middle after : Expr Value Var sort}
theorem words_append (first : Trace environment before middle) (second : Trace environment middle after) :
    words (first.append second) = words first ++ words second := by
  induction first with
  | nil => rfl
  | cons step tail previous => exact congrArg (List.cons _) (previous second)
end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
