import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Abel

/-!
# Source operation effect compiler

Finite typed expressions retain their source operations and intermediate carriers.
The compiler generates every additive, linear and bilinear effect from the old
source and its increment. Substitution and successive updates compose these effects;
no target equation or completed result is an input.
-/

set_option autoImplicit false

universe u v w w'

namespace SaturationMonoid.SourceOperationEffects

abbrev Env {Sorts : Type u} (Value : Sorts → Type v) (Var : Sorts → Type w) :=
  ∀ s, Var s → Value s

/-- The fixed source operations, with intermediate sorts retained. -/
inductive Expr {Sorts : Type u} (Value : Sorts → Type v) (Var : Sorts → Type w)
    [∀ s, AddCommGroup (Value s)] : Sorts → Type (max u v w)
  | var {s : Sorts} : Var s → Expr Value Var s
  | const {s : Sorts} : Value s → Expr Value Var s
  | add {s : Sorts} : Expr Value Var s → Expr Value Var s → Expr Value Var s
  | linear {s t : Sorts} : (Value s →+ Value t) → Expr Value Var s → Expr Value Var t
  | bilinear {s t r : Sorts} : (Value s →+ Value t →+ Value r) →
      Expr Value Var s → Expr Value Var t → Expr Value Var r

namespace Expr

variable {Sorts : Type u} {Value : Sorts → Type v}
  {Var : Sorts → Type w} {Var' : Sorts → Type w'}
  [∀ s, AddCommGroup (Value s)]

def eval {s : Sorts} : Expr Value Var s → Env Value Var → Value s
  | .var x, ρ => ρ _ x
  | .const c, _ => c
  | .add a b, ρ => eval a ρ + eval b ρ
  | .linear f a, ρ => f (eval a ρ)
  | .bilinear f a b, ρ => f (eval a ρ) (eval b ρ)

/-- Generate the effect from the old source and its actual increment.
The bilinear node keeps left, right, and joint action separately. -/
def effect {s : Sorts} : Expr Value Var s → Env Value Var → Env Value Var → Value s
  | .var x, _, δ => δ _ x
  | .const _, _, _ => 0
  | .add a b, ρ, δ => effect a ρ δ + effect b ρ δ
  | .linear f a, ρ, δ => f (effect a ρ δ)
  | .bilinear f a b, ρ, δ =>
      f (eval a ρ) (effect b ρ δ) + f (effect a ρ δ) (eval b ρ) +
        f (effect a ρ δ) (effect b ρ δ)

theorem eval_update {s : Sorts} (e : Expr Value Var s) (ρ δ : Env Value Var) :
    e.eval (ρ + δ) = e.eval ρ + e.effect ρ δ := by
  induction e with
  | var x => rfl
  | const c => exact (add_zero c).symm
  | add a b ha hb =>
      simp only [eval, effect, ha, hb]
      abel
  | linear f a ha => simp only [eval, effect, ha, map_add]
  | bilinear f a b ha hb =>
      simp only [eval, effect, ha, hb, map_add, AddMonoidHom.add_apply]
      abel

def subst {s : Sorts} (e : Expr Value Var s)
    (σ : ∀ t, Var t → Expr Value Var' t) : Expr Value Var' s :=
  match e with
  | .var x => σ _ x
  | .const c => .const c
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .linear f a => .linear f (a.subst σ)
  | .bilinear f a b => .bilinear f (a.subst σ) (b.subst σ)

theorem eval_subst {s : Sorts} (e : Expr Value Var s)
    (σ : ∀ t, Var t → Expr Value Var' t) (ρ : Env Value Var') :
    (e.subst σ).eval ρ = e.eval (fun t x => (σ t x).eval ρ) := by
  induction e with
  | var x => rfl
  | const c => rfl
  | add a b ha hb => simp only [subst, eval, ha, hb]
  | linear f a ha => simp only [subst, eval, ha]
  | bilinear f a b ha hb => simp only [subst, eval, ha, hb]

/-- Substitution composes the generated effects of arbitrarily nested source operations. -/
theorem effect_subst {s : Sorts} (e : Expr Value Var s)
    (σ : ∀ t, Var t → Expr Value Var' t) (ρ δ : Env Value Var') :
    (e.subst σ).effect ρ δ =
      e.effect (fun t x => (σ t x).eval ρ) (fun t x => (σ t x).effect ρ δ) := by
  induction e with
  | var x => rfl
  | const c => rfl
  | add a b ha hb => simp only [subst, effect, ha, hb]
  | linear f a ha => simp only [subst, effect, ha]
  | bilinear f a b ha hb => simp only [subst, effect, eval_subst, ha, hb]

theorem effect_zero {s : Sorts} (e : Expr Value Var s) (ρ : Env Value Var) :
    e.effect ρ 0 = 0 := by
  have h := e.eval_update ρ 0
  rw [add_zero] at h
  apply add_left_cancel (a := e.eval ρ)
  exact h.symm.trans (add_zero (e.eval ρ)).symm

/-- Two successive actual increments compose through the generated intermediate source. -/
theorem effect_add {s : Sorts} (e : Expr Value Var s) (ρ δ ε : Env Value Var) :
    e.effect ρ (δ + ε) = e.effect ρ δ + e.effect (ρ + δ) ε := by
  apply add_left_cancel (a := e.eval ρ)
  calc
    e.eval ρ + e.effect ρ (δ + ε) = e.eval (ρ + (δ + ε)) := (e.eval_update ρ _).symm
    _ = e.eval ((ρ + δ) + ε) := congrArg e.eval (add_assoc ρ δ ε).symm
    _ = e.eval ρ + (e.effect ρ δ + e.effect (ρ + δ) ε) := by
      rw [e.eval_update (ρ + δ) ε, e.eval_update ρ δ, add_assoc]

end Expr

end SaturationMonoid.SourceOperationEffects

