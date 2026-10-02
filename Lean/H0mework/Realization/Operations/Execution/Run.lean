import H0mework.Realization.Operations.Execution.Trace

/-! Recursive source execution visits the original syntax left-to-right and records each primitive computation. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationExecution

open SourceOperationEffects

universe u v w

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
variable [∀ sort, AddCommGroup (Value sort)]

def execution (environment : Env Value Var) {sort : Sorts} (expression : Expr Value Var sort) :
    Trace environment expression (.const (expression.eval environment)) :=
  match expression with
  | .var name => Trace.single (.bind name)
  | .const value => .nil (.const value)
  | .add left right =>
      ((execution environment left).addLeft right).append
        ((Trace.addRight (.const (left.eval environment)) (execution environment right)).append
          (Trace.single (.addConst (left.eval environment) (right.eval environment))))
  | .linear operation value =>
      (Trace.linear operation (execution environment value)).append
        (Trace.single (.linearConst operation (value.eval environment)))
  | .bilinear operation left right =>
      (Trace.bilinearLeft operation (execution environment left) right).append
        ((Trace.bilinearRight operation (.const (left.eval environment)) (execution environment right)).append
          (Trace.single (.bilinearConst operation (left.eval environment) (right.eval environment))))

theorem execution_length (environment : Env Value Var) {sort : Sorts} (expression : Expr Value Var sort) :
    (execution environment expression).length = remaining expression :=
  (execution environment expression).length_to_const

theorem completed_trace_value (environment : Env Value Var) {sort : Sorts}
    {expression : Expr Value Var sort} {value : Value sort}
    (trace : Trace environment expression (.const value)) : value = expression.eval environment :=
  trace.toDerivation.sound.symm

end SaturationMonoid.SourceOperationExecution
