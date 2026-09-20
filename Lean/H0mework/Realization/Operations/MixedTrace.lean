import H0mework.Realization.Operations.Effects
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Complete symbolic operation effects

An actual source increment generates an ordered list of typed mixed terms.
The construction keeps repeated occurrences and both orders of bilinear action.
Evaluation of the complete list is the effect produced by the composable compiler.
-/

set_option autoImplicit false

universe u v w

namespace SaturationMonoid.SourceOperationEffects

/-- A variable's position in the source update, not a choice of runtime disposition. -/
inductive UpdatePart
  | old
  | increment

abbrev ChangedVar {Sorts : Type u} (Var : Sorts → Type w) (s : Sorts) :=
  Var s × UpdatePart

def mixedEnvironment {Sorts : Type u} {Value : Sorts → Type v}
    {Var : Sorts → Type w} (ρ δ : Env Value Var) : Env Value (ChangedVar Var) :=
  fun s x => match x.2 with
    | .old => ρ s x.1
    | .increment => δ s x.1

namespace Expr

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)]

def old {s : Sorts} (e : Expr Value Var s) : Expr Value (ChangedVar Var) s :=
  e.subst (fun _ x => .var (x, .old))

theorem eval_old {s : Sorts} (e : Expr Value Var s) (ρ δ : Env Value Var) :
    e.old.eval (mixedEnvironment ρ δ) = e.eval ρ := by
  exact e.eval_subst (fun _ x => .var (x, .old)) (mixedEnvironment ρ δ)

/-- The complete generated mixed terms, retaining source order and multiplicity.
At a bilinear node the joint terms use the full ordered Cartesian product. -/
def mixedTerms {s : Sorts} : Expr Value Var s → List (Expr Value (ChangedVar Var) s)
  | .var x => [.var (x, .increment)]
  | .const _ => []
  | .add a b => a.mixedTerms ++ b.mixedTerms
  | .linear f a => a.mixedTerms.map (.linear f)
  | .bilinear f a b =>
      b.mixedTerms.map (.bilinear f a.old) ++
      a.mixedTerms.map (fun da => .bilinear f da b.old) ++
      a.mixedTerms.flatMap (fun da => b.mixedTerms.map (.bilinear f da))

def evalTerms {s : Sorts} : List (Expr Value Var s) → Env Value Var → Value s
  | [], _ => 0
  | e :: es, ρ => e.eval ρ + evalTerms es ρ

theorem evalTerms_eq_sum {s : Sorts} (es : List (Expr Value Var s))
    (ρ : Env Value Var) :
    evalTerms es ρ = (es.map (fun e => e.eval ρ)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [evalTerms, List.map_cons, List.sum_cons, ih]

theorem evalTerms_append {s : Sorts} (as bs : List (Expr Value Var s))
    (ρ : Env Value Var) :
    evalTerms (as ++ bs) ρ = evalTerms as ρ + evalTerms bs ρ := by
  induction as with
  | nil => simp only [List.nil_append, evalTerms, zero_add]
  | cons a as ih => simp only [List.cons_append, evalTerms, ih, add_assoc]

theorem evalTerms_linear {s t : Sorts} (f : Value s →+ Value t)
    (es : List (Expr Value Var s)) (ρ : Env Value Var) :
    evalTerms (es.map (.linear f)) ρ = f (evalTerms es ρ) := by
  induction es with
  | nil => simp only [List.map_nil, evalTerms, map_zero]
  | cons e es ih => simp only [List.map_cons, evalTerms, eval, ih, map_add]

theorem evalTerms_bilinear_right {s t r : Sorts}
    (f : Value s →+ Value t →+ Value r) (a : Expr Value Var s)
    (bs : List (Expr Value Var t)) (ρ : Env Value Var) :
    evalTerms (bs.map (.bilinear f a)) ρ = f (a.eval ρ) (evalTerms bs ρ) := by
  induction bs with
  | nil => simp only [List.map_nil, evalTerms, map_zero]
  | cons b bs ih => simp only [List.map_cons, evalTerms, eval, ih, map_add]

theorem evalTerms_bilinear_left {s t r : Sorts}
    (f : Value s →+ Value t →+ Value r) (as : List (Expr Value Var s))
    (b : Expr Value Var t) (ρ : Env Value Var) :
    evalTerms (as.map (fun a => .bilinear f a b)) ρ =
      f (evalTerms as ρ) (b.eval ρ) := by
  induction as with
  | nil => simp only [List.map_nil, evalTerms, map_zero, AddMonoidHom.zero_apply]
  | cons a as ih =>
      simp only [List.map_cons, evalTerms, eval, ih, map_add, AddMonoidHom.add_apply]

theorem evalTerms_bilinear_product {s t r : Sorts}
    (f : Value s →+ Value t →+ Value r)
    (as : List (Expr Value Var s)) (bs : List (Expr Value Var t))
    (ρ : Env Value Var) :
    evalTerms (as.flatMap (fun a => bs.map (.bilinear f a))) ρ =
      f (evalTerms as ρ) (evalTerms bs ρ) := by
  induction as with
  | nil => simp only [List.flatMap_nil, evalTerms, map_zero, AddMonoidHom.zero_apply]
  | cons a as ih =>
      simp only [List.flatMap_cons, evalTerms_append, evalTerms_bilinear_right,
        ih, evalTerms, map_add, AddMonoidHom.add_apply]

/-- Semantic completeness for arbitrary nesting and heterogeneous intermediate sorts. -/
theorem eval_mixedTerms {s : Sorts} (e : Expr Value Var s) (ρ δ : Env Value Var) :
    evalTerms e.mixedTerms (mixedEnvironment ρ δ) = e.effect ρ δ := by
  induction e with
  | var x => simp only [mixedTerms, evalTerms, eval, mixedEnvironment, add_zero, effect]
  | const c => rfl
  | add a b ha hb => simp only [mixedTerms, evalTerms_append, ha, hb, effect]
  | linear f a ha => simp only [mixedTerms, evalTerms_linear, ha, effect]
  | bilinear f a b ha hb =>
      simp only [mixedTerms, evalTerms_append, evalTerms_bilinear_right,
        evalTerms_bilinear_left, evalTerms_bilinear_product, eval_old, ha, hb, effect]

theorem mixedTerms_sum {s : Sorts} (e : Expr Value Var s) (ρ δ : Env Value Var) :
    (e.mixedTerms.map (fun term => term.eval (mixedEnvironment ρ δ))).sum =
      e.effect ρ δ :=
  (evalTerms_eq_sum e.mixedTerms (mixedEnvironment ρ δ)).symm.trans
    (e.eval_mixedTerms ρ δ)

/-- The source update directly consumes the complete symbolic effect trace. -/
theorem eval_update_mixedTerms {s : Sorts} (e : Expr Value Var s)
    (ρ δ : Env Value Var) :
    e.eval (ρ + δ) = e.eval ρ +
      (e.mixedTerms.map (fun term => term.eval (mixedEnvironment ρ δ))).sum := by
  rw [mixedTerms_sum]
  exact e.eval_update ρ δ

end Expr

end SaturationMonoid.SourceOperationEffects

