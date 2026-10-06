import H0mework.Realization.Operations.Execution.Trace
/-! Read the input and its complete paid trace from an executed linear map.
No inverse, quotient representative or new execution is selected. -/
set_option autoImplicit false
namespace SaturationMonoid.SourceOperationExecution
open SourceOperationEffects
universe u v w
variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ target, AddCommGroup (Value target)]
variable {environment : Env Value Var} {source target : Sorts} {operation : Value source →+ Value target}
def originalInput {expression : Expr Value Var source} {result : Value target} :
    Trace environment (.linear operation expression) (.const result) →
      Σ point : Value source, Trace environment expression (.const point) × PLift (operation point=result)
  | .cons (.linearConst _ point) rest => ⟨point,.nil _,⟨rest.sound⟩⟩
  | .cons (.linear _ step) rest =>
      let previous := originalInput rest
      ⟨previous.1,.cons step previous.2.1,previous.2.2⟩
termination_by trace => trace.length
decreasing_by
  simp only [Trace.length]
  omega
end SaturationMonoid.SourceOperationExecution
