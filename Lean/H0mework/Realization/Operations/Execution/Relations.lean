import H0mework.Realization.Operations.Execution.Trace
import H0mework.Realization.Operations.ScalarExact

/-! Actual execution steps generate typed relation words. Their boundary
retains the original endpoints and their effect under a source update. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationExecution

open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarDifferentialResidual

noncomputable section

universe r u v w

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}
variable {R : Type r} [CommRing R] [∀ s, Module R (Value s)]
variable {environment : Env Value Var} {before middle after : Expr Value Var s}

def Step.relationWords (step : Step environment before after) :
    RelationIndex R environment s →₀ R :=
  Finsupp.single (.inl ⟨before, after, step.toDerivation⟩) 1

theorem Step.relation_boundary (step : Step environment before after) :
    relationMap (R := R) environment step.relationWords =
      Finsupp.single before 1 - Finsupp.single after 1 := by
  simp only [Step.relationWords, relationMap, Finsupp.linearCombination_single, one_smul, relation]

def Trace.relationWords {before after : Expr Value Var s} :
    Trace environment before after → (RelationIndex R environment s →₀ R)
  | .nil _ => 0
  | .cons step tail => step.relationWords + tail.relationWords

theorem Trace.relation_boundary (trace : Trace environment before after) :
    relationMap (R := R) environment trace.relationWords =
      Finsupp.single before 1 - Finsupp.single after 1 := by
  induction trace with
  | nil expression => simp only [Trace.relationWords, map_zero, sub_self]
  | cons step tail ih =>
      rw [Trace.relationWords, map_add, Step.relation_boundary, ih]
      abel

theorem Trace.relationWords_append (first : Trace environment before middle)
    (second : Trace environment middle after) :
    (first.append second).relationWords (R := R) = first.relationWords + second.relationWords := by
  induction first with
  | nil expression => simp only [Trace.append, Trace.relationWords, zero_add]
  | cons step tail ih => simp only [Trace.append, Trace.relationWords, ih, add_assoc]

theorem Trace.relation_old (trace : Trace environment before after) :
    evaluation (R := R) environment (relationMap (R := R) environment trace.relationWords) = 0 :=
  LinearMap.congr_fun (evaluation_relationMap (R := R) (s := s) environment) trace.relationWords

theorem Trace.relation_inventory (trace : Trace environment before after) (increment : Env Value Var) :
    updateInventory (R := R) environment increment
        (relationMap (R := R) environment trace.relationWords) =
      (0, effectEvaluator (R := R) environment increment
        (relationMap (R := R) environment trace.relationWords)) := by
  exact Prod.ext (trace.relation_old (R := R)) rfl

theorem Trace.updated_residual (trace : Trace environment before after) (increment : Env Value Var) :
    (residualEquivRange (evaluation (R := R) (environment + increment))
      (canonicalResidual (evaluation (R := R) (environment + increment))
        (relationMap (R := R) environment trace.relationWords))).val =
      effectEvaluator (R := R) environment increment
        (relationMap (R := R) environment trace.relationWords) :=
  old_relation_updated_residual environment increment _ (trace.relation_old (R := R))

theorem Trace.updated_zero_iff (trace : Trace environment before after) (increment : Env Value Var) :
    canonicalResidual (evaluation (R := R) (environment + increment))
        (relationMap (R := R) environment trace.relationWords) = 0 ↔
      effectEvaluator (R := R) environment increment
        (relationMap (R := R) environment trace.relationWords) = 0 :=
  old_relation_updated_zero_iff environment increment _ (trace.relation_old (R := R))

theorem Trace.relation_cochain (trace : Trace environment before after) (increment : Env Value Var) :
    SourceOperationScalarCochain.boundary (R := R)
        (relationMap (R := R) environment trace.relationWords) ∈
      LinearMap.range (relationMap (R := R) (mixedEnvironment environment increment)) :=
  update_boundary_has_source_relations environment increment _

end
end SaturationMonoid.SourceOperationExecution
