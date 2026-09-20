import H0mework.Realization.Operations.ScalarRelations
import Mathlib.Algebra.Group.Prod

/-! The full old/effect inventory is itself a typed source-operation model. -/

set_option autoImplicit false

universe r u v w

namespace SaturationMonoid.SourceOperationScalarInventoryLift

open SourceOperationEffects SourceOperationScalarRelations

noncomputable section

variable {Sorts : Type u} (Value : Sorts → Type v)

abbrev PairValue (s : Sorts) := Value s × Value s

variable {Value} {Var : Sorts → Type w} [∀ s, AddCommGroup (Value s)]

def pairEnvironment (old increment : Env Value Var) : Env (PairValue Value) Var :=
  fun s x => (old s x, increment s x)

def pairLinear {s t : Sorts} (f : Value s →+ Value t) :
    PairValue Value s →+ PairValue Value t :=
  f.prodMap f

/-- Both ordered cross effects and the joint increment remain separate summands. -/
def pairBilinear {s t r : Sorts} (f : Value s →+ Value t →+ Value r) :
    PairValue Value s →+ PairValue Value t →+ PairValue Value r where
  toFun x :=
    ((f x.1).comp (AddMonoidHom.fst _ _)).prod
      (((f x.1).comp (AddMonoidHom.snd _ _) +
        (f x.2).comp (AddMonoidHom.fst _ _)) +
        (f x.2).comp (AddMonoidHom.snd _ _))
  map_zero' := by
    ext y <;> simp
  map_add' x y := by
    ext z <;> simp [map_add, add_left_comm, add_comm]

theorem pairBilinear_apply {s t r : Sorts} (f : Value s →+ Value t →+ Value r)
    (a da : Value s) (b db : Value t) :
    pairBilinear f (a, da) (b, db) =
      (f a b, f a db + f da b + f da db) := rfl

def liftExpr {s : Sorts} : Expr Value Var s → Expr (PairValue Value) Var s
  | .var x => .var x
  | .const value => .const (value, 0)
  | .add left right => .add (liftExpr left) (liftExpr right)
  | .linear f argument => .linear (pairLinear f) (liftExpr argument)
  | .bilinear f left right => .bilinear (pairBilinear f) (liftExpr left) (liftExpr right)

theorem eval_liftExpr {s : Sorts} (expression : Expr Value Var s)
    (old increment : Env Value Var) :
    (liftExpr expression).eval (pairEnvironment old increment) =
      (expression.eval old, expression.effect old increment) := by
  induction expression with
  | var x => rfl
  | const value => rfl
  | add left right hleft hright =>
      simp only [liftExpr, Expr.eval, hleft, hright, Expr.effect, Prod.mk_add_mk]
  | linear f argument hargument =>
      simp only [liftExpr, Expr.eval, hargument, Expr.effect, pairLinear,
        AddMonoidHom.coe_prodMap, Prod.map_apply]
  | bilinear f left right hleft hright =>
      simp only [liftExpr, Expr.eval, hleft, hright, Expr.effect, pairBilinear_apply]

variable {R : Type r} [CommRing R] [∀ s, Module R (Value s)]

abbrev liftMap {s : Sorts} : Formal R Value Var s →ₗ[R] Formal R (PairValue Value) Var s :=
  Finsupp.lmapDomain R R liftExpr

theorem evaluation_liftMap {s : Sorts} (old increment : Env Value Var) :
    (evaluation (R := R) (s := s) (pairEnvironment old increment)).comp liftMap =
      updateInventory (R := R) old increment := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp only [LinearMap.comp_apply, liftMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, evaluation, Finsupp.linearCombination_single,
    eval_liftExpr, updateInventory, effectEvaluator, LinearMap.prod_apply,
    Function.prod, Prod.smul_mk]

end

end SaturationMonoid.SourceOperationScalarInventoryLift
