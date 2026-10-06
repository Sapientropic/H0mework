import H0mework.Realization.Operations.Execution.Run

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor
open SaturationMonoid.SourceOperationEffects SaturationMonoid.SourceOperationExecution
namespace Extension
variable {S : Type u} (OldValue OldVar : S → Type u) (Output : Type u)
abbrev Slot := Sum S PUnit.{u+1}
abbrev Value : Slot (S:=S) → Type u
  | .inl slot => OldValue slot
  | .inr _ => Output
abbrev Var : Slot (S:=S) → Type u
  | .inl slot => OldVar slot
  | .inr _ => PEmpty.{u+1}
variable [∀ slot,AddCommGroup (OldValue slot)] [AddCommGroup Output]
instance : ∀ slot,AddCommGroup (Value OldValue Output slot)
  | .inl _ => inferInstance
  | .inr _ => inferInstance
def embed {slot : S} : Expr OldValue OldVar slot →
    Expr (Value OldValue Output) (Var OldVar) (.inl slot)
  | .var name => .var name
  | .const value => .const value
  | .add left right => .add (embed left) (embed right)
  | .linear operation argument => .linear operation (embed argument)
  | .bilinear operation left right => .bilinear operation (embed left) (embed right)
def environment (old : Env OldValue OldVar) : Env (Value OldValue Output) (Var OldVar)
  | .inl slot, name => old slot name
  | .inr _, absent => PEmpty.elim absent
theorem embed_eval {slot : S} (term : Expr OldValue OldVar slot) (old : Env OldValue OldVar) :
    (embed OldValue OldVar Output term).eval (environment OldValue OldVar Output old) = term.eval old := by
  induction term with
  | var => rfl
  | const => rfl
  | add left right first second => exact congrArg₂ (· + ·) first second
  | linear operation argument previous => exact congrArg operation previous
  | bilinear operation left right first second => exact congrArg₂ (fun a b => operation a b) first second
theorem embed_charge {slot : S} (term : Expr OldValue OldVar slot) :
    remaining (embed OldValue OldVar Output term) = remaining term := by
  induction term with
  | var => rfl
  | const => rfl
  | add left right first second => simp only [embed,remaining,first,second]
  | linear operation argument previous => simp only [embed,remaining,previous]
  | bilinear operation left right first second => simp only [embed,remaining,first,second]
end Extension

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
