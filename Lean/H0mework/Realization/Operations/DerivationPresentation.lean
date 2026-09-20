import H0mework.Realization.Operations.ScalarPresentation
import H0mework.Realization.Operations.IntegralRelations

/-! The integral presentation API is the specialization of the scalar source producer. -/

set_option autoImplicit false

universe u v w

namespace SaturationMonoid.SourceOperationPresentation

open SourceOperationEffects SourceOperationRelations SourceOperationDerivations
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

abbrev DerivationIndex (environment : Env Value Var) (s : Sorts) :=
  SourceOperationScalarPresentation.DerivationIndex environment s

abbrev RelationIndex (environment : Env Value Var) (s : Sorts) :=
  SourceOperationScalarPresentation.RelationIndex ℤ environment s

abbrev constantMap : (Value s →₀ ℤ) →ₗ[ℤ] Formal Value Var s :=
  SourceOperationScalarPresentation.constantMap (R := ℤ)

abbrev valueMap (environment : Env Value Var) : Formal Value Var s →ₗ[ℤ] (Value s →₀ ℤ) :=
  SourceOperationScalarPresentation.valueMap (R := ℤ) environment

theorem evaluation_constantMap (environment : Env Value Var) :
    (evaluation (s := s) environment).comp constantMap =
      ScalarRelationPresentation.freeEvaluation (R := ℤ) (Value s) :=
  SourceOperationScalarPresentation.evaluation_constantMap (R := ℤ) environment

theorem valueMap_evaluation (environment : Env Value Var) :
    (ScalarRelationPresentation.freeEvaluation (R := ℤ) (Value s)).comp (valueMap environment) =
      evaluation (s := s) environment :=
  SourceOperationScalarPresentation.valueMap_evaluation (R := ℤ) environment

abbrev relation (environment : Env Value Var) : RelationIndex environment s → Formal Value Var s :=
  SourceOperationScalarPresentation.relation (R := ℤ) environment

theorem relation_sound (environment : Env Value Var) (index : RelationIndex environment s) :
    evaluation environment (relation environment index) = 0 :=
  SourceOperationScalarPresentation.relation_sound (R := ℤ) environment index

abbrev relationMap (environment : Env Value Var) :
    (RelationIndex environment s →₀ ℤ) →ₗ[ℤ] Formal Value Var s :=
  SourceOperationScalarPresentation.relationMap (R := ℤ) environment

theorem evaluation_relationMap (environment : Env Value Var) :
    (evaluation (s := s) environment).comp (relationMap environment) = 0 :=
  SourceOperationScalarPresentation.evaluation_relationMap (R := ℤ) environment

abbrev normalizationCertificate (environment : Env Value Var) :
    Formal Value Var s →ₗ[ℤ] (RelationIndex environment s →₀ ℤ) :=
  SourceOperationScalarPresentation.normalizationCertificate (R := ℤ) environment

abbrev scalarCertificate (environment : Env Value Var) :
    (ScalarRelationPresentation.RelationIndex ℤ (Value s) →₀ ℤ) →ₗ[ℤ]
      (RelationIndex environment s →₀ ℤ) :=
  SourceOperationScalarPresentation.scalarCertificate (R := ℤ) environment

theorem source_reduction (environment : Env Value Var) (word : Formal Value Var s) :
    relationMap environment (normalizationCertificate environment word) =
      word - constantMap (valueMap environment word) :=
  SourceOperationScalarPresentation.source_reduction (R := ℤ) environment word

theorem scalarCertificate_read (environment : Env Value Var)
    (word : ScalarRelationPresentation.RelationIndex ℤ (Value s) →₀ ℤ) :
    relationMap environment (scalarCertificate environment word) =
      constantMap (ScalarRelationPresentation.relationMap (Value s) word) :=
  SourceOperationScalarPresentation.scalarCertificate_read (R := ℤ) environment word

theorem relation_range_eq_kernel (environment : Env Value Var) :
    LinearMap.range (relationMap (s := s) environment) = LinearMap.ker (evaluation environment) :=
  SourceOperationScalarPresentation.relation_range_eq_kernel (R := ℤ) environment

theorem residual_fibre_generated (environment : Env Value Var) (left right : Formal Value Var s) :
    SourceGeneratedScalarDifferentialResidual.canonicalResidual (evaluation environment) left =
        SourceGeneratedScalarDifferentialResidual.canonicalResidual (evaluation environment) right ↔
      left - right ∈ LinearMap.range (relationMap environment) :=
  SourceOperationScalarPresentation.residual_fibre_generated (R := ℤ) environment left right

end
end SaturationMonoid.SourceOperationPresentation
