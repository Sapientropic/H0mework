import H0mework.Realization.Operations.DerivationReduction
import Mathlib.Order.WellFounded
import Lean.Elab.Tactic.Omega

/-! Forward object execution counts source syntax steps, without treating primitive-internal cost as one of its claims. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationExecution

open SourceOperationEffects SourceOperationDerivations

universe u v w

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
variable [∀ sort, AddCommGroup (Value sort)]

def remaining {sort : Sorts} : Expr Value Var sort → Nat
  | .var _ => 1
  | .const _ => 0
  | .add left right => remaining left + remaining right + 1
  | .linear _ value => remaining value + 1
  | .bilinear _ left right => remaining left + remaining right + 1

inductive Step (environment : Env Value Var) :
    {sort : Sorts} → Expr Value Var sort → Expr Value Var sort → Type (max u v w)
  | bind {sort : Sorts} (name : Var sort) :
      Step environment (.var name) (.const (environment sort name))
  | addConst {sort : Sorts} (left right : Value sort) :
      Step environment (.add (.const left) (.const right)) (.const (left + right))
  | linearConst {source target : Sorts} (operation : Value source →+ Value target) (value : Value source) :
      Step environment (.linear operation (.const value)) (.const (operation value))
  | bilinearConst {leftSort rightSort target : Sorts}
      (operation : Value leftSort →+ Value rightSort →+ Value target)
      (left : Value leftSort) (right : Value rightSort) :
      Step environment (.bilinear operation (.const left) (.const right)) (.const (operation left right))
  | addLeft {sort : Sorts} {before after right : Expr Value Var sort} :
      Step environment before after → Step environment (.add before right) (.add after right)
  | addRight {sort : Sorts} {left before after : Expr Value Var sort} :
      Step environment before after → Step environment (.add left before) (.add left after)
  | linear {source target : Sorts} (operation : Value source →+ Value target)
      {before after : Expr Value Var source} :
      Step environment before after → Step environment (.linear operation before) (.linear operation after)
  | bilinearLeft {leftSort rightSort target : Sorts}
      (operation : Value leftSort →+ Value rightSort →+ Value target)
      {before after : Expr Value Var leftSort} {right : Expr Value Var rightSort} :
      Step environment before after →
        Step environment (.bilinear operation before right) (.bilinear operation after right)
  | bilinearRight {leftSort rightSort target : Sorts}
      (operation : Value leftSort →+ Value rightSort →+ Value target)
      {left : Expr Value Var leftSort} {before after : Expr Value Var rightSort} :
      Step environment before after →
        Step environment (.bilinear operation left before) (.bilinear operation left after)

namespace Step

def toDerivation {environment : Env Value Var} {sort : Sorts} {before after : Expr Value Var sort} :
    Step environment before after → Derivation environment before after
  | .bind name => .bind name
  | .addConst left right => .addConst left right
  | .linearConst operation value => .linearConst operation value
  | .bilinearConst operation left right => .bilinearConst operation left right
  | .addLeft step => .addCongr step.toDerivation (.refl _)
  | .addRight step => .addCongr (.refl _) step.toDerivation
  | .linear operation step => .linearCongr operation step.toDerivation
  | .bilinearLeft operation step => .bilinearCongr operation step.toDerivation (.refl _)
  | .bilinearRight operation step => .bilinearCongr operation (.refl _) step.toDerivation

theorem remaining_eq {environment : Env Value Var} {sort : Sorts} {before after : Expr Value Var sort}
    (step : Step environment before after) : remaining before = remaining after + 1 := by
  induction step <;> simp_all [remaining] <;> omega

theorem sound {environment : Env Value Var} {sort : Sorts} {before after : Expr Value Var sort}
    (step : Step environment before after) : before.eval environment = after.eval environment :=
  step.toDerivation.sound

end Step

theorem const_no_step (environment : Env Value Var) {sort : Sorts}
    (value : Value sort) (target : Expr Value Var sort) : ¬ Nonempty (Step environment (.const value) target) := by
  rintro ⟨step⟩
  nomatch step

theorem step_wellFounded (environment : Env Value Var) (sort : Sorts) :
    WellFounded (fun after before : Expr Value Var sort => Nonempty (Step environment before after)) := by
  have decreases : ∀ after before : Expr Value Var sort,
      Nonempty (Step environment before after) → remaining after < remaining before := by
    rintro after before ⟨step⟩
    have decrease := step.remaining_eq
    omega
  exact Subrelation.wf (fun {after before} step => decreases after before step) (measure remaining).wf

end SaturationMonoid.SourceOperationExecution
