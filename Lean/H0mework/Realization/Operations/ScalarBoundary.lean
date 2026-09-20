import H0mework.Realization.Operations.MixedTrace
import H0mework.Realization.Operations.ScalarRelations

/-! The source operation and its complete mixed trace generate a formal boundary. -/

set_option autoImplicit false

universe r u v w

namespace SaturationMonoid.SourceOperationScalarCochain

open SourceOperationEffects SourceOperationScalarRelations

noncomputable section

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

abbrev updated (expression : Expr Value Var s) : Expr Value (ChangedVar Var) s :=
  expression.subst (fun _ x => .add (.var (x, .old)) (.var (x, .increment)))

theorem eval_updated (expression : Expr Value Var s) (old increment : Env Value Var) :
    (updated expression).eval (mixedEnvironment old increment) =
      expression.eval (old + increment) :=
  expression.eval_subst _ _

variable {R : Type r} [CommRing R] [∀ s, Module R (Value s)]

abbrev traceWord (terms : List (Expr Value Var s)) : Formal R Value Var s :=
  (terms.map (fun term => Finsupp.single term (1 : R))).sum

theorem evaluation_traceWord (terms : List (Expr Value Var s)) (environment : Env Value Var) :
    evaluation (R := R) environment (traceWord terms) =
      (terms.map (fun term => term.eval environment)).sum := by
  induction terms with
  | nil => exact map_zero _
  | cons term terms ih =>
      change evaluation (R := R) environment (Finsupp.single term 1 + traceWord terms) = _
      rw [map_add, ih]
      simp only [evaluation, Finsupp.linearCombination_single, one_smul,
        List.map_cons, List.sum_cons]

/-- The source syntax fixes both update endpoints and every mixed occurrence. -/
abbrev updateWord (expression : Expr Value Var s) : Formal R Value (ChangedVar Var) s :=
  Finsupp.single (updated expression) 1 - Finsupp.single expression.old 1 -
    traceWord expression.mixedTerms

theorem evaluation_updateWord (expression : Expr Value Var s) (old increment : Env Value Var) :
    evaluation (R := R) (mixedEnvironment old increment) (updateWord expression) = 0 := by
  unfold updateWord
  rw [map_sub, map_sub, evaluation_traceWord]
  simp only [evaluation, Finsupp.linearCombination_single, one_smul,
    eval_updated, Expr.eval_old]
  rw [expression.eval_update_mixedTerms old increment]
  abel

/-- Linearize the generated equations, without accepting an equation or differential law. -/
abbrev boundary : Formal R Value Var s →ₗ[R] Formal R Value (ChangedVar Var) s :=
  Finsupp.linearCombination R updateWord

omit [∀ s, Module R (Value s)] in
theorem boundary_single (expression : Expr Value Var s) (coefficient : R) :
    boundary (Finsupp.single expression coefficient) = coefficient • updateWord expression :=
  Finsupp.linearCombination_single _ _ _

theorem evaluation_boundary (old increment : Env Value Var) :
    (evaluation (R := R) (s := s) (mixedEnvironment old increment)).comp boundary = 0 := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp only [LinearMap.comp_apply, boundary_single, map_smul,
    evaluation_updateWord, smul_zero, LinearMap.zero_apply]

theorem boundary_range_le_kernel (old increment : Env Value Var) :
    LinearMap.range (boundary (R := R) (Value := Value) (Var := Var) (s := s)) ≤
      LinearMap.ker (evaluation (R := R) (mixedEnvironment old increment)) :=
  LinearMap.range_le_ker_iff.mpr (evaluation_boundary old increment)

end
end SaturationMonoid.SourceOperationScalarCochain
