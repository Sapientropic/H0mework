import H0mework.Realization.Operations.Execution.Relations.History.Events
import H0mework.Realization.Completion.FaithfulRealization
/-! A fixed paid prefix supplies the relation history; continuation preserves that prefix. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
open CofinalHistorySettlement
variable {Sorts : Type u} {Value Var : Sorts → Type u}
variable [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {before after : Expr Value Var sort}
def continuation : RootedAccountedUnfolding
    (PresentedRelationEventAt (Expr Value Var sort) → RootedAccountedUnfolding
      (PresentedRelationEventAt (Expr Value Var sort))) := .zero RootedAccountedUnfolding.zero

variable {Root : Type u}
variable (rootOccurrence : RootedAccountedUnfolding Root)
abbrev history (trace : Trace environment before after) :=
  RootGeneratedCofinalHistoryAt.generate (rootOccurrence:=rootOccurrence)
    (seedOccurrence:=exposure trace) (continuationOccurrence:=continuation (Value:=Value) (Var:=Var))

def evaluator (environment : Env Value Var) : RootedAccountedUnfolding
    (Expr Value Var sort → Value sort) := .zero (fun expression => expression.eval environment)
abbrev face (trace : Trace environment before after) :=
  CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
    (history:=history rootOccurrence trace) (evaluatorOccurrence:=evaluator environment)

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
