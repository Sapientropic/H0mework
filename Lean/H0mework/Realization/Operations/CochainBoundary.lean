import H0mework.Realization.Operations.ScalarBoundary
import H0mework.Realization.Operations.IntegralRelations

/-! The original integral API specializes the shared scalar producer to ℤ. -/

set_option autoImplicit false

universe u v w

namespace SaturationMonoid.SourceOperationCochain

open SourceOperationEffects SourceOperationRelations

noncomputable section

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

abbrev updated (expression : Expr Value Var s) : Expr Value (ChangedVar Var) s :=
  SourceOperationScalarCochain.updated expression

theorem eval_updated (expression : Expr Value Var s) (old increment : Env Value Var) :
    (updated expression).eval (mixedEnvironment old increment) = expression.eval (old + increment) :=
  SourceOperationScalarCochain.eval_updated expression old increment

abbrev traceWord (terms : List (Expr Value Var s)) : Formal Value Var s :=
  SourceOperationScalarCochain.traceWord (R := ℤ) terms

theorem evaluation_traceWord (terms : List (Expr Value Var s)) (environment : Env Value Var) :
    evaluation environment (traceWord terms) = (terms.map (fun term => term.eval environment)).sum :=
  SourceOperationScalarCochain.evaluation_traceWord (R := ℤ) terms environment

abbrev updateWord (expression : Expr Value Var s) : Formal Value (ChangedVar Var) s :=
  SourceOperationScalarCochain.updateWord (R := ℤ) expression

theorem evaluation_updateWord (expression : Expr Value Var s) (old increment : Env Value Var) :
    evaluation (mixedEnvironment old increment) (updateWord expression) = 0 :=
  SourceOperationScalarCochain.evaluation_updateWord (R := ℤ) expression old increment

abbrev boundary : Formal Value Var s →ₗ[ℤ] Formal Value (ChangedVar Var) s :=
  SourceOperationScalarCochain.boundary (R := ℤ)

theorem boundary_single (expression : Expr Value Var s) (coefficient : ℤ) :
    boundary (Finsupp.single expression coefficient) = coefficient • updateWord expression :=
  SourceOperationScalarCochain.boundary_single (R := ℤ) expression coefficient

theorem evaluation_boundary (old increment : Env Value Var) :
    (evaluation (s := s) (mixedEnvironment old increment)).comp boundary = 0 :=
  SourceOperationScalarCochain.evaluation_boundary (R := ℤ) old increment

theorem boundary_range_le_kernel (old increment : Env Value Var) :
    LinearMap.range (boundary (Value := Value) (Var := Var) (s := s)) ≤
      LinearMap.ker (evaluation (mixedEnvironment old increment)) :=
  SourceOperationScalarCochain.boundary_range_le_kernel (R := ℤ) old increment

end
end SaturationMonoid.SourceOperationCochain
