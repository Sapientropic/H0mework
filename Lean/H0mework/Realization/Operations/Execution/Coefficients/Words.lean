import H0mework.Realization.Operations.Execution.Coefficients.Source
import H0mework.Realization.Operations.InventoryLift
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! The retained word supplies every original term and integer coefficient.
Each coefficient expands before execution; finite support order comes from
the source word and no completed value constructs the expression. -/

set_option autoImplicit false
noncomputable section
universe u v w
namespace SaturationMonoid.SourceOperationExecution.Coefficients
open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open SaturationMonoid.SourceOperationExecution
variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

def terms (items : List (Expr Value Var sort × ℤ)) : Expr Value Var sort :=
  match items with
  | [] => .const 0
  | (argument, integer) :: rest => .add (integerExpansion integer argument) (terms rest)

def termsCost (items : List (Expr Value Var sort × ℤ)) : Nat :=
  match items with
  | [] => 0
  | (argument, integer) :: rest => integerSourceCost integer (remaining argument) + termsCost rest + 1

theorem terms_eval (items : List (Expr Value Var sort × ℤ)) (environment : Env Value Var) :
    (terms items).eval environment = (items.map (fun item => item.2 • item.1.eval environment)).sum := by
  induction items with
  | nil => rfl
  | cons item rest prior =>
      rcases item with ⟨argument, integer⟩
      simp only [terms, Expr.eval, integerExpansion_eval, prior, List.map_cons, List.sum_cons]

theorem terms_remaining (items : List (Expr Value Var sort × ℤ)) :
    remaining (terms items) = termsCost items := by
  induction items with
  | nil => rfl
  | cons item rest prior =>
      rcases item with ⟨argument, integer⟩
      simp only [terms, termsCost, remaining, integerExpansion_remaining, prior]

def sourceItems (word : Formal ℤ Value Var sort) : List (Expr Value Var sort × ℤ) :=
  word.support.toList.map (fun term => (term, word term))

def expression (word : Formal ℤ Value Var sort) : Expr Value Var sort := terms (sourceItems word)

def cost (word : Formal ℤ Value Var sort) : Nat := termsCost (sourceItems word)

theorem expression_eval (word : Formal ℤ Value Var sort) (environment : Env Value Var) :
    (expression word).eval environment = evaluation (R := ℤ) environment word := by
  classical
  rw [expression, terms_eval, sourceItems, evaluation, Finsupp.linearCombination_apply]
  simp only [List.map_map, Finsupp.sum]
  exact Finset.sum_map_toList _ _

theorem expression_effect (word : Formal ℤ Value Var sort) (environment increment : Env Value Var) :
    (expression word).effect environment increment = effectEvaluator (R := ℤ) environment increment word := by
  apply add_left_cancel (a := (expression word).eval environment)
  rw [← Expr.eval_update, expression_eval, expression_eval]
  exact LinearMap.congr_fun (evaluation_update (R := ℤ) environment increment) word

theorem expression_remaining (word : Formal ℤ Value Var sort) :
    remaining (expression word) = cost word := terms_remaining (sourceItems word)

def expressionTrace (word : Formal ℤ Value Var sort) (environment : Env Value Var) :
    Trace environment (expression word) (.const (evaluation (R := ℤ) environment word)) :=
  (expression_eval word environment) ▸ execution environment (expression word)

theorem expressionTrace_cost (word : Formal ℤ Value Var sort) (environment : Env Value Var) :
    (expressionTrace word environment).length = cost word :=
  (expressionTrace word environment).length_to_const.trans (expression_remaining word)

private theorem liftExpr_remaining (argument : Expr Value Var sort) :
    remaining (liftExpr argument) = remaining argument := by
  induction argument with
  | var => rfl
  | const => rfl
  | add _ _ first second => simp only [liftExpr, remaining, first, second]
  | linear _ _ prior => simp only [liftExpr, remaining, prior]
  | bilinear _ _ _ first second => simp only [liftExpr, remaining, first, second]

theorem lifted_remaining (word : Formal ℤ Value Var sort) :
    remaining (liftExpr (expression word)) = cost word :=
  (liftExpr_remaining (expression word)).trans (expression_remaining word)

end SaturationMonoid.SourceOperationExecution.Coefficients
