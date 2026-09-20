import H0mework.Realization.Operations.DerivationReduction
import H0mework.Realization.Operations.ScalarRelations
import H0mework.Foundation.Relations.ScalarPresentation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Source proof trees and the source module laws generate the complete semantic relation kernel over any commutative ring. -/

set_option autoImplicit false

universe r u v w

namespace SaturationMonoid.SourceOperationScalarPresentation

open SourceOperationEffects SourceOperationScalarRelations SourceOperationDerivations
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

abbrev DerivationIndex (environment : Env Value Var) (s : Sorts) :=
  Σ left right : Expr Value Var s, Derivation environment left right

abbrev RelationIndex (R : Type r) [CommRing R] [∀ s, Module R (Value s)]
    (environment : Env Value Var) (s : Sorts) :=
  DerivationIndex environment s ⊕ ScalarRelationPresentation.RelationIndex R (Value s)

variable {R : Type r} [CommRing R] [∀ s, Module R (Value s)]

abbrev constantMap : (Value s →₀ R) →ₗ[R] Formal R Value Var s :=
  Finsupp.lmapDomain R R Expr.const

abbrev valueMap (environment : Env Value Var) : Formal R Value Var s →ₗ[R] (Value s →₀ R) :=
  Finsupp.lmapDomain R R (fun expression => expression.eval environment)

theorem evaluation_constantMap (environment : Env Value Var) :
    (evaluation (R := R) (s := s) environment).comp (constantMap (R := R)) =
      ScalarRelationPresentation.freeEvaluation (R := R) (Value s) := by
  unfold evaluation constantMap
  rw [Finsupp.linearCombination_comp_lmapDomain]
  rfl

theorem valueMap_evaluation (environment : Env Value Var) :
    (ScalarRelationPresentation.freeEvaluation (R := R) (Value s)).comp
        (valueMap (R := R) environment) =
      evaluation (R := R) (s := s) environment := by
  unfold ScalarRelationPresentation.freeEvaluation valueMap
  rw [Finsupp.linearCombination_comp_lmapDomain]
  rfl

/-- Proof-tree endpoints and the existing source module relations generate every relation. -/
abbrev relation (environment : Env Value Var) : RelationIndex R environment s → Formal R Value Var s
  | .inl derivation => Finsupp.single derivation.1 1 - Finsupp.single derivation.2.1 1
  | .inr scalar => constantMap (R := R)
      (ScalarRelationPresentation.relation (R := R) (Value s) scalar)

theorem relation_sound (environment : Env Value Var) (index : RelationIndex R environment s) :
    evaluation (R := R) environment (relation (R := R) environment index) = 0 := by
  cases index with
  | inl derivation =>
      simp only [relation, map_sub, evaluation, Finsupp.linearCombination_single, one_smul]
      exact sub_eq_zero.mpr derivation.2.2.sound
  | inr scalar =>
      change evaluation (R := R) environment (constantMap (R := R) _) = 0
      rw [← LinearMap.comp_apply, evaluation_constantMap]
      exact ScalarRelationPresentation.freeEvaluation_relation (R := R) (Value s) scalar

abbrev relationMap (environment : Env Value Var) :
    (RelationIndex R environment s →₀ R) →ₗ[R] Formal R Value Var s :=
  Finsupp.linearCombination R (relation (R := R) environment)

theorem evaluation_relationMap (environment : Env Value Var) :
    (evaluation (R := R) (s := s) environment).comp (relationMap (R := R) environment) = 0 := by
  apply Finsupp.lhom_ext
  intro index coefficient
  simp only [LinearMap.comp_apply, relationMap, Finsupp.linearCombination_single,
    map_smul, relation_sound, smul_zero, LinearMap.zero_apply]

/-- Each input expression generates its own finite reduction proof. -/
abbrev normalizationCertificate (environment : Env Value Var) :
    Formal R Value Var s →ₗ[R] (RelationIndex R environment s →₀ R) :=
  Finsupp.linearCombination R (fun expression =>
    Finsupp.single (.inl ⟨expression, .const (expression.eval environment),
      Derivation.normalize environment expression⟩) 1)

abbrev scalarCertificate (environment : Env Value Var) :
    (ScalarRelationPresentation.RelationIndex R (Value s) →₀ R) →ₗ[R]
      (RelationIndex R environment s →₀ R) :=
  Finsupp.lmapDomain R R Sum.inr

theorem source_reduction (environment : Env Value Var) (word : Formal R Value Var s) :
    relationMap (R := R) environment (normalizationCertificate (R := R) environment word) =
      word - constantMap (R := R) (valueMap (R := R) environment word) := by
  have reduction : (relationMap (R := R) environment).comp
        (normalizationCertificate (R := R) environment) =
      LinearMap.id - (constantMap (R := R)).comp
        (valueMap (R := R) (s := s) environment) := by
    apply Finsupp.lhom_ext
    intro expression coefficient
    simp [relationMap, normalizationCertificate, relation, constantMap, valueMap,
      Finsupp.lmapDomain_apply, smul_sub]
  exact LinearMap.congr_fun reduction word

theorem scalarCertificate_read (environment : Env Value Var)
    (word : ScalarRelationPresentation.RelationIndex R (Value s) →₀ R) :
    relationMap (R := R) environment (scalarCertificate (R := R) environment word) =
      constantMap (R := R) (ScalarRelationPresentation.relationMap (R := R) (Value s) word) := by
  have factorization : (relationMap (R := R) environment).comp
        (scalarCertificate (R := R) environment) =
      (constantMap (R := R)).comp (ScalarRelationPresentation.relationMap (R := R) (Value s)) := by
    apply Finsupp.lhom_ext
    intro index coefficient
    simp [relationMap, scalarCertificate, relation, Finsupp.lmapDomain_apply]
  exact LinearMap.congr_fun factorization word

theorem relation_range_eq_kernel (environment : Env Value Var) :
    LinearMap.range (relationMap (R := R) (s := s) environment) =
      LinearMap.ker (evaluation (R := R) environment) := by
  apply le_antisymm (LinearMap.range_le_ker_iff.mpr (evaluation_relationMap (R := R) environment))
  intro word killed
  have valueKilled : ScalarRelationPresentation.freeEvaluation (R := R) (Value s)
      (valueMap (R := R) environment word) = 0 := by
    rw [← LinearMap.comp_apply, valueMap_evaluation]
    exact killed
  have valueQuotient :
      (Submodule.Quotient.mk (valueMap (R := R) environment word) :
        ScalarRelationPresentation.PresentedCarrier R (Value s)) = 0 := by
    apply (ScalarRelationPresentation.presentedEquiv (R := R) (Value s)).injective
    change ScalarRelationPresentation.freeEvaluation (R := R) (Value s)
      (valueMap (R := R) environment word) = _
    rw [valueKilled, map_zero]
  have valueRelation : valueMap (R := R) environment word ∈
      LinearMap.range (ScalarRelationPresentation.relationMap (R := R) (Value s)) :=
    (Submodule.Quotient.mk_eq_zero _).mp valueQuotient
  obtain ⟨scalarWord, scalarRead⟩ := valueRelation
  refine ⟨normalizationCertificate (R := R) environment word +
    scalarCertificate (R := R) environment scalarWord, ?_⟩
  rw [map_add, source_reduction, scalarCertificate_read, scalarRead, sub_add_cancel]

theorem residual_fibre_generated (environment : Env Value Var) (left right : Formal R Value Var s) :
    SourceGeneratedScalarDifferentialResidual.canonicalResidual (evaluation (R := R) environment) left =
        SourceGeneratedScalarDifferentialResidual.canonicalResidual
          (evaluation (R := R) environment) right ↔
      left - right ∈ LinearMap.range (relationMap (R := R) environment) := by
  rw [relation_range_eq_kernel]
  exact residual_fibre_iff (R := R) environment left right

end
end SaturationMonoid.SourceOperationScalarPresentation
