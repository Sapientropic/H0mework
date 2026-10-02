import H0mework.Realization.Operations.Execution.Step

/-! Finite forward traces retain every intermediate expression and step before generating semantic proofs. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationExecution

open SourceOperationEffects SourceOperationDerivations

universe u v w

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
variable [∀ sort, AddCommGroup (Value sort)]

inductive Trace (environment : Env Value Var) :
    {sort : Sorts} → Expr Value Var sort → Expr Value Var sort → Type (max u v w)
  | nil {sort : Sorts} (expression : Expr Value Var sort) : Trace environment expression expression
  | cons {sort : Sorts} {before middle after : Expr Value Var sort} :
      Step environment before middle → Trace environment middle after → Trace environment before after

namespace Trace

variable {environment : Env Value Var} {sort : Sorts}
variable {before middle after : Expr Value Var sort}

def length {before after : Expr Value Var sort} : Trace environment before after → Nat
  | .nil _ => 0
  | .cons _ tail => 1 + tail.length

def single (step : Step environment before after) : Trace environment before after :=
  .cons step (.nil after)

def append {before middle after : Expr Value Var sort}
    (first : Trace environment before middle) (second : Trace environment middle after) :
    Trace environment before after :=
  match first with
  | .nil _ => second
  | .cons step tail => .cons step (tail.append second)

def toDerivation {before after : Expr Value Var sort} : Trace environment before after → Derivation environment before after
  | .nil expression => .refl expression
  | .cons step tail => .trans step.toDerivation tail.toDerivation

theorem remaining_eq (trace : Trace environment before after) :
    remaining before = trace.length + remaining after := by
  induction trace with
  | nil expression => simp [length]
  | cons step tail previous =>
      simp only [length]
      have decrease := step.remaining_eq
      omega

theorem length_to_const {value : Value sort} (trace : Trace environment before (.const value)) :
    trace.length = remaining before := by
  have accounting := trace.remaining_eq
  simpa only [remaining, Nat.add_zero] using accounting.symm

theorem sound (trace : Trace environment before after) : before.eval environment = after.eval environment :=
  trace.toDerivation.sound

def addLeft {before after : Expr Value Var sort} (trace : Trace environment before after) (right : Expr Value Var sort) :
    Trace environment (.add before right) (.add after right) :=
  match trace with
  | .nil expression => .nil (.add expression right)
  | .cons step tail => .cons (.addLeft step) (tail.addLeft right)

def addRight {before after : Expr Value Var sort} (left : Expr Value Var sort) (trace : Trace environment before after) :
    Trace environment (.add left before) (.add left after) :=
  match trace with
  | .nil expression => .nil (.add left expression)
  | .cons step tail => .cons (.addRight step) (addRight left tail)

def linear {target : Sorts} {before after : Expr Value Var sort}
    (operation : Value sort →+ Value target) (trace : Trace environment before after) :
    Trace environment (.linear operation before) (.linear operation after) :=
  match trace with
  | .nil expression => .nil (.linear operation expression)
  | .cons step tail => .cons (.linear operation step) (linear operation tail)

def bilinearLeft {rightSort target : Sorts} {before after : Expr Value Var sort}
    (operation : Value sort →+ Value rightSort →+ Value target)
    (trace : Trace environment before after) (right : Expr Value Var rightSort) :
    Trace environment (.bilinear operation before right) (.bilinear operation after right) :=
  match trace with
  | .nil expression => .nil (.bilinear operation expression right)
  | .cons step tail => .cons (.bilinearLeft operation step) (bilinearLeft operation tail right)

def bilinearRight {leftSort target : Sorts} {before after : Expr Value Var sort}
    (operation : Value leftSort →+ Value sort →+ Value target)
    (left : Expr Value Var leftSort) (trace : Trace environment before after) :
    Trace environment (.bilinear operation left before) (.bilinear operation left after) :=
  match trace with
  | .nil expression => .nil (.bilinear operation left expression)
  | .cons step tail => .cons (.bilinearRight operation step) (bilinearRight operation left tail)

end Trace
end SaturationMonoid.SourceOperationExecution
