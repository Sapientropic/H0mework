import H0mework.Realization.HomotopyLimits.Sequential
import Mathlib.Algebra.Category.ModuleCat.Products

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SequentialHomotopyLimit

open CategoryTheory CategoryTheory.Limits
open RootGeneratedSequentialHomotopyLimitAt

private def sequentialPreimage {A : Nat → Type u} [∀ n, AddCommGroup (A n)]
    (lift : ∀ n, A n → A (n+1)) (target : ∀ n, A n) : ∀ n, A n
  | 0 => 0
  | n+1 => lift n (sequentialPreimage lift target n - target n)

private theorem sequential_difference_surjective {A : Nat → Type u} [∀ n, AddCommGroup (A n)]
    (step : ∀ n, A (n+1) → A n) (onto : ∀ n, Function.Surjective (step n)) :
    Function.Surjective (fun value : ∀ n, A n => fun n => value n - step n (value (n+1))) := by
  let lift := fun n value => Classical.choose (onto n value)
  intro target
  let value := sequentialPreimage lift target
  refine ⟨value, funext (fun n => ?_)⟩
  have paid : step n (lift n (value n - target n)) = value n - target n :=
    Classical.choose_spec (onto n (value n - target n))
  change value n - step n (lift n (value n - target n)) = target n
  rw [paid, sub_sub_cancel]

variable {Root : Type w}
variable {occurrence : RootedAccountedUnfolding (Root × (ℕᵒᵖ ⥤ IntegralCochainComplex))}
variable (face : RootGeneratedSequentialHomotopyLimitAt occurrence)

private def degreeCoordinates (degree : ℤ) :=
  face.productXIso degree ≪≫ ModuleCat.piIsoPi (fun n : Nat => (face.towerObject n).X degree)

private theorem degree_coordinates_apply (degree : ℤ) (value : face.productComplex.X degree) (n : Nat) :
    ((degreeCoordinates face degree).hom value) n = (face.productProjection n).f degree value := by
  let first := face.productXIso degree
  let terms := fun k : Nat => (face.towerObject k).X degree
  let second := ModuleCat.piIsoPi terms
  have read := ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype terms n) (first.hom value)
  change (second.hom (first.hom value)) n = (Pi.π terms n) (first.hom value) at read
  exact read.trans (ConcreteCategory.congr_hom (face.productXIso_hom_comp_π degree n) value)

private theorem difference_coordinate (degree : ℤ) (value : face.productComplex.X degree) (n : Nat) :
    ((degreeCoordinates face degree).hom (face.difference.f degree value)) n =
      ((degreeCoordinates face degree).hom value) n -
        (face.transitionAt n).f degree (((degreeCoordinates face degree).hom value) (n+1)) := by
  have read := congrArg (fun (map : face.productComplex ⟶ face.towerObject n) => map.f degree)
    (face.difference_projection n)
  rw [degree_coordinates_apply, degree_coordinates_apply, degree_coordinates_apply]
  exact ConcreteCategory.congr_hom read value

/-- The actual compatibility difference is onto in every degree if the actual adjacent maps are onto. -/
theorem difference_epi_of_surjective
    (onto : ∀ (degree : ℤ) (stage : Nat), Function.Surjective ((face.transitionAt stage).f degree)) :
    Epi face.difference := by
  apply HomologicalComplex.epi_of_epi_f
  intro degree
  apply (ModuleCat.epi_iff_surjective _).2
  intro target
  let coordinates := degreeCoordinates face degree
  obtain ⟨solution, solves⟩ := sequential_difference_surjective
    (fun n => fun value => (face.transitionAt n).f degree value) (onto degree) (coordinates.hom target)
  let selected := coordinates.inv solution
  have chosen : coordinates.hom selected = solution :=
    ConcreteCategory.congr_hom coordinates.inv_hom_id solution
  refine ⟨selected, coordinates.toLinearEquiv.injective ?_⟩
  change coordinates.hom (face.difference.f degree selected) = coordinates.hom target
  funext n
  rw [difference_coordinate face degree selected n, chosen]
  exact congrFun solves n

end SequentialHomotopyLimit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
