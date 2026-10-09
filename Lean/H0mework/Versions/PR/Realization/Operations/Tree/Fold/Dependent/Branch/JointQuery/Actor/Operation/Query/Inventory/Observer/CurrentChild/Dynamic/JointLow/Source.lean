import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Source
import H0mework.Realization.Operations.Execution.Substitution.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow
open SourceOperationEffects SourceOperationExecution
variable {S : Type u} {A X : S → Type u} [∀ slot, AddCommGroup (A slot)]
abbrev Variable (slot : S) := Sum (X slot) (X slot)
def leftBinding (slot : S) (name : X slot) : Expr A (Variable (X:=X)) slot := .var (.inl name)
def rightBinding (slot : S) (name : X slot) : Expr A (Variable (X:=X)) slot := .var (.inr name)
def environment (left right : Env A X) : Env A (Variable (X:=X)) :=
 fun slot name => match name with | .inl first => left slot first | .inr second => right slot second
def left {slot : S} (term : Expr A X slot) := term.subst leftBinding
def right {slot : S} (term : Expr A X slot) := term.subst rightBinding
def expression {slot : S} (first second : Expr A X slot) := (left first).add (right second)
def raw {slot : S} (firstEnvironment secondEnvironment : Env A X) (first second : Expr A X slot) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=A) (Var:=Variable (X:=X)) (sort:=slot) :=
 ⟨environment firstEnvironment secondEnvironment,expression first second⟩
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.JointLow
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
