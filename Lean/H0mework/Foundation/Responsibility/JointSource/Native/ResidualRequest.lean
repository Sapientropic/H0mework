import H0mework.Foundation.Responsibility.JointSource.Source
import H0mework.Realization.Operations.Execution.Relations

/-! A paid source relation becomes an executable request after its actual
environment update. Its value is generated; no zero or nonzero branch is input. -/

set_option autoImplicit false
universe u r

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.ResidualRequest

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation
open SourceGeneratedScalarDifferentialResidual

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
  {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}

structure MaterialAt
    (occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current) : Type u where
  environment : Env Value Var
  increment : Env Value Var
  raw : Expr Value Var sort
  state : SourceOperationExecutionDebt.State environment raw
  owner : OpenResponsibilityAt N (lower.source.source.toRootSource.account.supportOf occurrence)

variable {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current}
  (material : MaterialAt (Value := Value) (Var := Var) (sort := sort) occurrence)

def expression : Expr Value Var sort :=
  .add material.raw (.linear (-AddMonoidHom.id (Value sort)) material.state.1)

def input : RawInputAt (Value := Value) (Var := Var) (sort := sort) lower current occurrence where
  environment := material.environment + material.increment
  expression := expression material
  owner := material.owner

theorem expression_eval (environment : Env Value Var) :
    (expression material).eval environment =
      material.raw.eval environment - material.state.1.eval environment := by
  simp only [expression, Expr.eval, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, sub_eq_add_neg]

theorem old_value : (expression material).eval material.environment = 0 := by
  rw [expression_eval, material.state.2.sound, sub_self]

theorem budget : remaining (expression material) =
    remaining material.raw + remaining material.state.1 + 2 := by
  simp only [expression, remaining]
  omega

theorem action_is_paid : ∃ paid,
    SourceOperationExecutionDebt.generate (input material).environment (expression material)
      (SourceOperationExecutionDebt.initial (input material).environment (expression material)) =
        .inr paid := by
  cases generated : SourceOperationExecutionDebt.generate (input material).environment (expression material)
      (SourceOperationExecutionDebt.initial (input material).environment (expression material)) with
  | inl settled =>
      have zero := (SourceOperationExecutionDebt.law
        (input material).environment (expression material)).settlement_budget_zero settled
      change remaining (expression material) = 0 at zero
      rw [budget] at zero
      omega
  | inr paid => exact ⟨paid, rfl⟩

variable {R : Type r} [CommRing R] [∀ sort, Module R (Value sort)]

def relations := material.state.2.relationWords (R := R)

theorem relation_boundary : relationMap (R := R) material.environment (relations (R := R) material) =
    Finsupp.single material.raw (1 : R) - Finsupp.single material.state.1 (1 : R) :=
  material.state.2.relation_boundary

theorem updated_value : (expression material).eval (input material).environment =
    effectEvaluator (R := R) material.environment material.increment
      (relationMap (R := R) material.environment (relations (R := R) material)) := by
  rw [relation_boundary]
  simp only [effectEvaluator, map_sub, Finsupp.linearCombination_single, one_smul]
  change (expression material).eval (material.environment + material.increment) = _
  rw [expression_eval, Expr.eval_update, Expr.eval_update, material.state.2.sound]
  abel

theorem residual_value :
    (residualEquivRange (evaluation (R := R) (input material).environment)
      (canonicalResidual (evaluation (R := R) (input material).environment)
        (relationMap (R := R) material.environment (relations (R := R) material)))).val =
      (expression material).eval (input material).environment := by
  exact (material.state.2.updated_residual (R := R) material.increment).trans
    (updated_value (R := R) material).symm

theorem residual_zero_iff :
    canonicalResidual (evaluation (R := R) (input material).environment)
        (relationMap (R := R) material.environment (relations (R := R) material)) = 0 ↔
      (expression material).eval (input material).environment = 0 := by
  exact (material.state.2.updated_zero_iff (R := R) material.increment).trans
    (by rw [updated_value (R := R) material]; rfl)

end
end RootGeneratedDebtActivationJointSource.Native.ResidualRequest
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
