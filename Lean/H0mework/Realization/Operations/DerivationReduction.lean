import H0mework.Realization.Operations.Effects

/-!
Object-level derivations retain the source binding and operation at every step.
Normalization is generated recursively from those steps in `Type`; no semantic
equation or normalizer is supplied as a constructor input.
-/

set_option autoImplicit false

universe u v w w'

namespace SaturationMonoid.SourceOperationDerivations

open SourceOperationEffects

variable {Sorts : Type u} {Value : Sorts → Type v}
  {Var : Sorts → Type w} {Var' : Sorts → Type w'}
  [∀ s, AddCommGroup (Value s)]

inductive Derivation (ρ : Env Value Var) :
    {s : Sorts} → Expr Value Var s → Expr Value Var s → Type (max u v w)
  | refl {s : Sorts} (e : Expr Value Var s) : Derivation ρ e e
  | symm {s : Sorts} {a b : Expr Value Var s} :
      Derivation ρ a b → Derivation ρ b a
  | trans {s : Sorts} {a b c : Expr Value Var s} :
      Derivation ρ a b → Derivation ρ b c → Derivation ρ a c
  | bind {s : Sorts} (x : Var s) :
      Derivation ρ (.var x) (.const (ρ s x))
  | addConst {s : Sorts} (a b : Value s) :
      Derivation ρ (.add (.const a) (.const b)) (.const (a + b))
  | linearConst {s t : Sorts} (f : Value s →+ Value t) (a : Value s) :
      Derivation ρ (.linear f (.const a)) (.const (f a))
  | bilinearConst {s t r : Sorts}
      (f : Value s →+ Value t →+ Value r) (a : Value s) (b : Value t) :
      Derivation ρ (.bilinear f (.const a) (.const b)) (.const (f a b))
  | addCongr {s : Sorts} {a a' b b' : Expr Value Var s} :
      Derivation ρ a a' → Derivation ρ b b' →
        Derivation ρ (.add a b) (.add a' b')
  | linearCongr {s t : Sorts} (f : Value s →+ Value t)
      {a a' : Expr Value Var s} :
      Derivation ρ a a' → Derivation ρ (.linear f a) (.linear f a')
  | bilinearCongr {s t r : Sorts} (f : Value s →+ Value t →+ Value r)
      {a a' : Expr Value Var s} {b b' : Expr Value Var t} :
      Derivation ρ a a' → Derivation ρ b b' →
        Derivation ρ (.bilinear f a b) (.bilinear f a' b')

namespace Derivation

theorem sound {ρ : Env Value Var} {s : Sorts} {a b : Expr Value Var s}
    (d : Derivation ρ a b) : a.eval ρ = b.eval ρ := by
  induction d with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | bind _ => rfl
  | addConst _ _ => rfl
  | linearConst _ _ => rfl
  | bilinearConst _ _ _ => rfl
  | addCongr _ _ ih₁ ih₂ => exact congrArg₂ (· + ·) ih₁ ih₂
  | linearCongr f _ ih => exact congrArg f ih
  | bilinearCongr f _ _ ih₁ ih₂ => exact congrArg₂ (fun x y => f x y) ih₁ ih₂

/-- Produce a replayable derivation from each original syntax node. -/
def normalize (ρ : Env Value Var) {s : Sorts} (e : Expr Value Var s) :
    Derivation ρ e (.const (e.eval ρ)) :=
  match e with
  | .var x => .bind x
  | .const a => .refl (.const a)
  | .add a b =>
      .trans (.addCongr (normalize ρ a) (normalize ρ b))
        (.addConst (a.eval ρ) (b.eval ρ))
  | .linear f a =>
      .trans (.linearCongr f (normalize ρ a)) (.linearConst f (a.eval ρ))
  | .bilinear f a b =>
      .trans (.bilinearCongr f (normalize ρ a) (normalize ρ b))
        (.bilinearConst f (a.eval ρ) (b.eval ρ))

/-- Equality of the two already-evaluated endpoints transports their generated
normalizations. This characterizes the semantic fibre; it does not decide it. -/
def of_eval_eq (ρ : Env Value Var) {s : Sorts} (a b : Expr Value Var s)
    (h : a.eval ρ = b.eval ρ) : Derivation ρ a b :=
  .trans (normalize ρ a) (h ▸ (normalize ρ b).symm)

theorem nonempty_iff {ρ : Env Value Var} {s : Sorts} (a b : Expr Value Var s) :
    Nonempty (Derivation ρ a b) ↔ a.eval ρ = b.eval ρ :=
  ⟨fun ⟨d⟩ => d.sound, fun h => ⟨of_eval_eq ρ a b h⟩⟩

/-- Substituting an original variable binding runs the substituted source term's
normalization in the target environment; no commuting equation is an input. -/
def subst (σ : ∀ s, Var s → Expr Value Var' s) (ρ : Env Value Var')
    {s : Sorts} {a b : Expr Value Var s}
    (d : Derivation (fun t x => (σ t x).eval ρ) a b) :
    Derivation ρ (a.subst σ) (b.subst σ) :=
  match d with
  | .refl e => .refl (e.subst σ)
  | .symm d => (subst σ ρ d).symm
  | .trans d₁ d₂ => .trans (subst σ ρ d₁) (subst σ ρ d₂)
  | .bind x => normalize ρ (σ _ x)
  | .addConst x y => .addConst x y
  | .linearConst f x => .linearConst f x
  | .bilinearConst f x y => .bilinearConst f x y
  | .addCongr d₁ d₂ => .addCongr (subst σ ρ d₁) (subst σ ρ d₂)
  | .linearCongr f d => .linearCongr f (subst σ ρ d)
  | .bilinearCongr f d₁ d₂ => .bilinearCongr f (subst σ ρ d₁) (subst σ ρ d₂)

end Derivation

end SaturationMonoid.SourceOperationDerivations
