import H0mework.Realization.Operations.ScalarComplex
import H0mework.Realization.Operations.CochainBoundary

/-! The original integral API specializes the shared scalar producer to ℤ. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.SourceOperationCochain

open SourceOperationEffects SourceOperationRelations CategoryTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ s, AddCommGroup (Value s)] {s : Sorts}

abbrev shortComplex (old increment : Env Value Var) : ShortComplex (ModuleCat.{u} ℤ) :=
  SourceOperationScalarCochain.shortComplex (R := ℤ) (s := s) old increment

abbrev cochain (old increment : Env Value Var) : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  SourceOperationScalarCochain.cochain (R := ℤ) (s := s) old increment

theorem cochain_d₀ (old increment : Env Value Var) :
    (cochain (s := s) old increment).d 0 1 = ModuleCat.ofHom boundary :=
  SourceOperationScalarCochain.cochain_d₀ (R := ℤ) old increment

theorem cochain_d₁ (old increment : Env Value Var) :
    (cochain (s := s) old increment).d 1 2 =
      ModuleCat.ofHom (evaluation (mixedEnvironment old increment)) :=
  SourceOperationScalarCochain.cochain_d₁ (R := ℤ) old increment

theorem presented_boundary_evaluation (old increment : Env Value Var)
    (word : ScalarRelationPresentation.PresentedCarrier ℤ (Formal Value Var s)) :
    ScalarRelationPresentation.presentedEquiv (R := ℤ) (Value s)
      (ScalarRelationPresentation.presentedMap (evaluation (mixedEnvironment old increment))
        (ScalarRelationPresentation.presentedMap boundary word)) = 0 :=
  SourceOperationScalarCochain.presented_boundary_evaluation (R := ℤ) old increment word

theorem boundary_generator_relation_factorization (old increment : Env Value Var) :
    (ScalarRelationPresentation.generatorMap
        (evaluation (s := s) (mixedEnvironment old increment))).comp
      (ScalarRelationPresentation.generatorMap boundary) =
    (ScalarRelationPresentation.relationMap (R := ℤ) (Value s)).comp
      (ScalarRelationPresentation.zeroRelationLift (R := ℤ)
        (Formal Value Var s) (Value s)) :=
  SourceOperationScalarCochain.boundary_generator_relation_factorization (R := ℤ) old increment

theorem cochain_presented_comp_zero (old increment : Env Value Var)
    (word : ScalarRelationPresentation.PresentedCarrier ℤ
      ((cochain (s := s) old increment).X 0)) :
    ScalarRelationPresentation.presentedEquiv (R := ℤ) ((cochain old increment).X 2)
      (ScalarRelationPresentation.presentedMap ((cochain old increment).d 1 2).hom
        (ScalarRelationPresentation.presentedMap ((cochain old increment).d 0 1).hom word)) = 0 :=
  SourceOperationScalarCochain.cochain_presented_comp_zero (R := ℤ) old increment word

abbrev generatedHomology (old increment : Env Value Var) :
    (shortComplex (s := s) old increment).LeftHomologyData :=
  SourceOperationScalarCochain.generatedHomology (R := ℤ) old increment

theorem boundary_is_cycle (old increment : Env Value Var) (word : Formal Value Var s) :
    ((shortComplex old increment).moduleCatToCycles word).val = boundary word :=
  SourceOperationScalarCochain.boundary_is_cycle (R := ℤ) old increment word

theorem update_fibre_iff (old increment : Env Value Var)
    (left right : Formal Value (ChangedVar Var) s) :
    (shortComplex old increment).pOpcycles left =
        (shortComplex old increment).pOpcycles right ↔
      left - right ∈ LinearMap.range boundary :=
  SourceOperationScalarCochain.update_fibre_iff (R := ℤ) old increment left right

end
end SaturationMonoid.SourceOperationCochain
