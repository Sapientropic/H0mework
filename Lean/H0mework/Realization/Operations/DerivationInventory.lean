import H0mework.Realization.Operations.InventoryLift
import H0mework.Realization.Operations.IntegralRelations

/-! The original integral API specializes the shared scalar producer to ℤ. -/

set_option autoImplicit false

universe u v w

namespace SaturationMonoid.SourceOperationInventoryLift

open SourceOperationEffects SourceOperationRelations

noncomputable section

variable {Sorts : Type u} (Value : Sorts → Type v)

abbrev PairValue (s : Sorts) := SourceOperationScalarInventoryLift.PairValue Value s

variable {Value} {Var : Sorts → Type w} [∀ s, AddCommGroup (Value s)]

abbrev pairEnvironment (old increment : Env Value Var) : Env (PairValue Value) Var :=
  SourceOperationScalarInventoryLift.pairEnvironment old increment

abbrev pairLinear {s t : Sorts} (f : Value s →+ Value t) :
    PairValue Value s →+ PairValue Value t := SourceOperationScalarInventoryLift.pairLinear f

abbrev pairBilinear {s t r : Sorts} (f : Value s →+ Value t →+ Value r) :
    PairValue Value s →+ PairValue Value t →+ PairValue Value r :=
  SourceOperationScalarInventoryLift.pairBilinear f

theorem pairBilinear_apply {s t r : Sorts} (f : Value s →+ Value t →+ Value r)
    (a da : Value s) (b db : Value t) :
    pairBilinear f (a, da) (b, db) = (f a b, f a db + f da b + f da db) :=
  SourceOperationScalarInventoryLift.pairBilinear_apply f a da b db

abbrev liftExpr {s : Sorts} : Expr Value Var s → Expr (PairValue Value) Var s :=
  SourceOperationScalarInventoryLift.liftExpr

theorem eval_liftExpr {s : Sorts} (expression : Expr Value Var s)
    (old increment : Env Value Var) :
    (liftExpr expression).eval (pairEnvironment old increment) =
      (expression.eval old, expression.effect old increment) :=
  SourceOperationScalarInventoryLift.eval_liftExpr expression old increment

abbrev liftMap {s : Sorts} : Formal Value Var s →ₗ[ℤ] Formal (PairValue Value) Var s :=
  SourceOperationScalarInventoryLift.liftMap (R := ℤ)

theorem evaluation_liftMap {s : Sorts} (old increment : Env Value Var) :
    (evaluation (s := s) (pairEnvironment old increment)).comp liftMap =
      updateInventory old increment :=
  SourceOperationScalarInventoryLift.evaluation_liftMap (R := ℤ) old increment

end
end SaturationMonoid.SourceOperationInventoryLift
