import H0mework.Realization.Operations.ScalarPresentation
import H0mework.Realization.Operations.InventoryLift
import H0mework.Realization.Operations.ScalarBoundary

/-! The generated semantic relations supply exactness and retain the full old/effect inventory fibre. -/

set_option autoImplicit false

universe r u v w

namespace SaturationMonoid.SourceOperationScalarPresentation

open SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open CategoryTheory

noncomputable section

section ArbitraryUniverses

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}
variable {R : Type r} [CommRing R] [∀ s, Module R (Value s)]

theorem update_boundary_has_source_relations (old increment : Env Value Var)
    (word : Formal R Value Var s) :
    SourceOperationScalarCochain.boundary (R := R) word ∈
      LinearMap.range (relationMap (R := R) (mixedEnvironment old increment)) := by
  rw [relation_range_eq_kernel, LinearMap.mem_ker]
  exact LinearMap.congr_fun (SourceOperationScalarCochain.evaluation_boundary (R := R) old increment) word

theorem inventory_fibre_generated (old increment : Env Value Var)
    (left right : Formal R Value Var s) :
    updateInventory (R := R) old increment left = updateInventory (R := R) old increment right ↔
      liftMap (R := R) (left - right) ∈ LinearMap.range (relationMap (R := R) (pairEnvironment old increment)) := by
  rw [relation_range_eq_kernel, LinearMap.mem_ker, ← LinearMap.comp_apply,
    evaluation_liftMap, map_sub, sub_eq_zero]

end ArbitraryUniverses

variable {R : Type r} [CommRing R]
variable {Sorts : Type u} {Value Var : Sorts → Type (max r u)}
  [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}

/-- Local source derivations and existing scalar relations supply the complete semantic kernel. -/
def presentationComplex (environment : Env Value Var) : ShortComplex (ModuleCat.{max r u} R) :=
  ShortComplex.moduleCatMk (relationMap (R := R) (s := s) environment) (evaluation (R := R) environment)
    (evaluation_relationMap (R := R) environment)

theorem presentationComplex_exact (environment : Env Value Var) :
    (presentationComplex (R := R) (s := s) environment).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact relation_range_eq_kernel (R := R) environment

end
end SaturationMonoid.SourceOperationScalarPresentation
