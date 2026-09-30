import H0mework.Realization.ScalarCofinal.KernelCompletion
import Mathlib.Data.Finset.Lattice.Fold

/-!
# A common source representative for finitely many completion coordinates

One representative of the highest quotient coordinate descends through the
existing source and limit naturality squares. The result is a Generator vector
matching a finite prefix, with no simultaneous choice of representatives at infinity.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalKernelCompletion.Data

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {Carrier : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier stage)] [∀ stage, Module R (Carrier stage)]
variable (data : Data (R := R) (Generator := Generator) (Carrier := Carrier))
variable (compatible : data.Compatible)

theorem finite_lift (point : data.Completion compatible) (bound : Nat) :
    ∃ source : Generator, ∀ stage ≤ bound,
      data.quotientMap stage source = (data.restriction compatible stage).hom point := by
  obtain ⟨source, sourceAtBound⟩ := Submodule.mkQ_surjective (data.stageKernel bound)
    ((data.restriction compatible bound).hom point)
  change data.quotientMap bound source = (data.restriction compatible bound).hom point at sourceAtBound
  refine ⟨source, ?_⟩
  intro stage stage_le_bound
  let arrow : Opposite.op bound ⟶ Opposite.op stage := (homOfLE stage_le_bound).op
  have sourceSquare := (data.sourceState compatible).naturality arrow
  simp only [Functor.const_obj_map] at sourceSquare
  have sourceAt := ConcreteCategory.congr_hom sourceSquare source
  change data.quotientMap stage source =
    ((data.quotientTower compatible).map arrow).hom (data.quotientMap bound source) at sourceAt
  have limitAt := ConcreteCategory.congr_hom (limit.w (data.quotientTower compatible) arrow) point
  change ((data.quotientTower compatible).map arrow).hom
      ((data.restriction compatible bound).hom point) =
    (data.restriction compatible stage).hom point at limitAt
  exact sourceAt.trans
    ((congrArg ((data.quotientTower compatible).map arrow).hom sourceAtBound).trans limitAt)

theorem finset_lift (point : data.Completion compatible) (stages : Finset Nat) :
    ∃ source : Generator, ∀ stage ∈ stages,
      data.quotientMap stage source = (data.restriction compatible stage).hom point := by
  obtain ⟨source, agreement⟩ := data.finite_lift compatible point (stages.sup id)
  exact ⟨source, fun stage member => agreement stage (Finset.le_sup (f := id) member)⟩

end

end SourceGeneratedScalarCofinalKernelCompletion.Data
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
