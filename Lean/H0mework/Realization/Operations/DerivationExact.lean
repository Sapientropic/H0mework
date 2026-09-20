import H0mework.Realization.Operations.ScalarExact
import H0mework.Realization.Operations.DerivationPresentation
import H0mework.Realization.Operations.DerivationInventory
import H0mework.Realization.Operations.CochainBoundary

/-! The original integral API specializes the shared scalar producer to ℤ. -/

set_option autoImplicit false

universe u v w

namespace SaturationMonoid.SourceOperationPresentation

open SourceOperationEffects SourceOperationRelations SourceOperationInventoryLift CategoryTheory

noncomputable section

section ArbitraryUniverses

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

theorem update_boundary_has_source_relations (old increment : Env Value Var)
    (word : Formal Value Var s) :
    SourceOperationCochain.boundary word ∈
      LinearMap.range (relationMap (mixedEnvironment old increment)) :=
  SourceOperationScalarPresentation.update_boundary_has_source_relations (R := ℤ) old increment word

theorem inventory_fibre_generated (old increment : Env Value Var)
    (left right : Formal Value Var s) :
    updateInventory old increment left = updateInventory old increment right ↔
      liftMap (left - right) ∈ LinearMap.range (relationMap (pairEnvironment old increment)) :=
  SourceOperationScalarPresentation.inventory_fibre_generated (R := ℤ) old increment left right

end ArbitraryUniverses

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

abbrev presentationComplex (environment : Env Value Var) : ShortComplex (ModuleCat.{u} ℤ) :=
  SourceOperationScalarPresentation.presentationComplex (R := ℤ) (s := s) environment

theorem presentationComplex_exact (environment : Env Value Var) :
    (presentationComplex (s := s) environment).Exact :=
  SourceOperationScalarPresentation.presentationComplex_exact (R := ℤ) environment

end
end SaturationMonoid.SourceOperationPresentation
