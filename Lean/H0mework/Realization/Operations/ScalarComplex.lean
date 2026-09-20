import H0mework.Realization.Operations.ScalarBoundary
import H0mework.Foundation.Relations.ScalarCochain
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! The generated boundary supplies the actual cochain law and existing homology consumers. -/

set_option autoImplicit false

universe r u

namespace SaturationMonoid.SourceOperationScalarCochain

open SourceOperationEffects SourceOperationScalarRelations CategoryTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {R : Type r} [CommRing R]
variable {Sorts : Type u} {Value Var : Sorts → Type (max r u)}
  [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}

def shortComplex (old increment : Env Value Var) : ShortComplex (ModuleCat.{max r u} R) :=
  ShortComplex.moduleCatMk (boundary (R := R) (s := s)) (evaluation (R := R) (mixedEnvironment old increment))
    (evaluation_boundary (R := R) old increment)

/-- The first two differentials are the actual syntax boundary and evaluation.
The remaining degrees are the usual zero extension of this short complex. -/
def cochain (old increment : Env Value Var) : CochainComplex (ModuleCat.{max r u} R) ℕ :=
  let source := shortComplex (R := R) (s := s) old increment
  CochainComplex.mk source.X₁ source.X₂ source.X₃ source.f source.g source.zero
    (fun _ => ⟨ModuleCat.of R PUnit, 0, CategoryTheory.Limits.comp_zero⟩)

theorem cochain_d₀ (old increment : Env Value Var) :
    (cochain (R := R) (s := s) old increment).d 0 1 = ModuleCat.ofHom (boundary (R := R)) := by
  simp only [cochain, CochainComplex.mk_d_1_0]
  rfl

theorem cochain_d₁ (old increment : Env Value Var) :
    (cochain (R := R) (s := s) old increment).d 1 2 =
      ModuleCat.ofHom (evaluation (R := R) (mixedEnvironment old increment)) := by
  simp only [cochain, CochainComplex.mk_d_2_0]
  rfl

theorem presented_boundary_evaluation (old increment : Env Value Var)
    (word : ScalarRelationPresentation.PresentedCarrier R (Formal R Value Var s)) :
    ScalarRelationPresentation.presentedEquiv (R := R) (Value s)
      (ScalarRelationPresentation.presentedMap (evaluation (R := R) (mixedEnvironment old increment))
        (ScalarRelationPresentation.presentedMap (R := R) (boundary (R := R)) word)) = 0 := by
  rw [ScalarRelationPresentation.presentedMap_commutes,
    ScalarRelationPresentation.presentedMap_commutes]
  exact LinearMap.congr_fun (evaluation_boundary (R := R) old increment) _

theorem boundary_generator_relation_factorization (old increment : Env Value Var) :
    (ScalarRelationPresentation.generatorMap (R := R)
        (evaluation (R := R) (s := s) (mixedEnvironment old increment))).comp
      (ScalarRelationPresentation.generatorMap (R := R) (boundary (R := R))) =
    (ScalarRelationPresentation.relationMap (R := R) (Value s)).comp
      (ScalarRelationPresentation.zeroRelationLift (R := R)
        (Formal R Value Var s) (Value s)) :=
  ScalarRelationPresentation.generatorMap_comp_factorizes_through_zeroRelation
    (boundary (R := R)) (evaluation (R := R) (mixedEnvironment old increment)) (evaluation_boundary (R := R) old increment)

theorem cochain_presented_comp_zero (old increment : Env Value Var)
    (word : ScalarRelationPresentation.PresentedCarrier R
      ((cochain (R := R) (s := s) old increment).X 0)) :
    ScalarRelationPresentation.presentedEquiv (R := R) ((cochain (R := R) old increment).X 2)
      (ScalarRelationPresentation.presentedMap ((cochain (R := R) old increment).d 1 2).hom
        (ScalarRelationPresentation.presentedMap ((cochain (R := R) old increment).d 0 1).hom word)) = 0 := by
  rw [ScalarRelationPresentation.presentedMap_commutes,
    ScalarRelationPresentation.presentedMap_commutes]
  exact ConcreteCategory.congr_hom ((cochain (R := R) old increment).d_comp_d 0 1 2)
    (ScalarRelationPresentation.presentedEquiv (R := R) ((cochain (R := R) old increment).X 0) word)

/-- Existing homology retains semantic cycles not yet supplied by the update boundary. -/
def generatedHomology (old increment : Env Value Var) :
    (shortComplex (R := R) (s := s) old increment).LeftHomologyData :=
  (shortComplex (R := R) old increment).moduleCatLeftHomologyData

theorem boundary_is_cycle (old increment : Env Value Var) (word : Formal R Value Var s) :
    ((shortComplex (R := R) old increment).moduleCatToCycles word).val = boundary (R := R) word := rfl

theorem update_fibre_iff (old increment : Env Value Var)
    (left right : Formal R Value (ChangedVar Var) s) :
    (shortComplex (R := R) old increment).pOpcycles left =
        (shortComplex (R := R) old increment).pOpcycles right ↔
      left - right ∈ LinearMap.range (boundary (R := R)) :=
  (shortComplex (R := R) old increment).moduleCat_pOpcycles_eq_iff left right

end
end SaturationMonoid.SourceOperationScalarCochain
