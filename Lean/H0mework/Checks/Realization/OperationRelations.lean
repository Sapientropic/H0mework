import H0mework.Realization.Operations.IntegralRelations
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

/-! Preserved additive relations and a source-generated nonzero relation effect. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationRelations.Controls

open SourceOperationEffects
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarDifferentialResidual

noncomputable section

section AdditiveIdentity

variable {Sorts : Type*} {Value : Sorts → Type*} {Var : Sorts → Type*}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

def addRelation (left right : Expr Value Var s) : Formal Value Var s :=
  Finsupp.single (.add left right) 1 - Finsupp.single left 1 - Finsupp.single right 1

theorem source_add_relation_zero (left right : Expr Value Var s) (ρ : Env Value Var) :
    evaluation ρ (addRelation left right) = 0 := by
  simp [evaluation, addRelation, Expr.eval]

theorem source_add_relation_effect_zero (left right : Expr Value Var s)
    (ρ δ : Env Value Var) : effectEvaluator ρ δ (addRelation left right) = 0 := by
  simp [effectEvaluator, addRelation, Expr.effect]

theorem source_add_relation_remains_zero (left right : Expr Value Var s)
    (ρ δ : Env Value Var) :
    canonicalResidual (evaluation (ρ + δ)) (addRelation left right) = 0 :=
  (old_relation_updated_zero_iff ρ δ (addRelation left right)
    (source_add_relation_zero left right ρ)).2 (source_add_relation_effect_zero left right ρ δ)

end AdditiveIdentity

abbrev ScalarValue : Unit → Type := fun _ => ℤ
abbrev ScalarVar : Unit → Type := fun _ => Unit

def xTerm : Expr ScalarValue ScalarVar () := .var ()

def square : Expr ScalarValue ScalarVar () :=
  .bilinear (s := ()) (t := ()) AddMonoidHom.mul xTerm xTerm

def accidentalRelation : Formal ScalarValue ScalarVar () :=
  Finsupp.single square 1 - Finsupp.single xTerm 1

def one : Env ScalarValue ScalarVar := fun _ _ => 1

theorem accidental_old_relation_zero : evaluation one accidentalRelation = 0 := by
  norm_num [evaluation, accidentalRelation, square, xTerm, one, Expr.eval,
    AddMonoidHom.mul_apply]

theorem actual_increment_generates_nonzero_effect :
    effectEvaluator one one accidentalRelation = 2 := by
  norm_num [effectEvaluator, accidentalRelation, square, xTerm, one, Expr.effect,
    Expr.eval, AddMonoidHom.mul_apply]

theorem actual_increment_generates_nonzero_residual :
    canonicalResidual (evaluation (one + one)) accidentalRelation ≠ 0 := by
  apply (old_relation_updated_nonzero_iff one one accidentalRelation
    accidental_old_relation_zero).2
  rw [actual_increment_generates_nonzero_effect]
  decide

theorem old_zero_does_not_supply_updated_kernel :
    ¬ LinearMap.ker (evaluation (s := ()) one) ≤ LinearMap.ker (evaluation (s := ()) (one + one)) := by
  intro inclusion
  have old_mem : accidentalRelation ∈ LinearMap.ker (evaluation one) :=
    accidental_old_relation_zero
  exact actual_increment_generates_nonzero_residual
    ((canonicalResidual_eq_zero_iff _ _).2 (inclusion old_mem))

end

end SaturationMonoid.SourceOperationRelations.Controls
