import H0mework.Realization.Operations.ObservationModel

/-! Actual action words enlarge the existing reader inventory before its original model is formed. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords

open SourceGeneratedActionObservationHistory

noncomputable section
universe r u
variable {R : Type r} [CommRing R]
variable {I C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (actions : I → C →ₗ[R] C) (read : C →ₗ[R] B)

def run : List I → C →ₗ[R] C
  | [] => 1
  | letter :: rest => run rest * actions letter

theorem run_append (left right : List I) : run actions (left ++ right) = run actions right * run actions left := by
  induction left with
  | nil => simp [run]
  | cons letter rest previous =>
      simp only [List.cons_append, run, previous, mul_assoc]

def inventory : C →ₗ[R] (List I → B) :=
  LinearMap.pi (fun word => read.comp (run actions word))

theorem inventory_apply (value : C) (word : List I) :
    inventory actions read value word = read (run actions word value) := rfl

theorem kernel_invariant (letter : I) :
    LinearMap.ker (inventory actions read) ≤ (LinearMap.ker (inventory actions read)).comap (actions letter) := by
  intro value invisible
  change inventory actions read (actions letter value) = 0
  funext word
  exact congrFun invisible (letter :: word)

theorem kernel_invisible : LinearMap.ker (inventory actions read) ≤ LinearMap.ker read := by
  intro value invisible
  exact congrFun invisible []

theorem original_kernel (primary : I) :
    LinearMap.ker (sourceMap (actions primary) (inventory actions read)) =
      LinearMap.ker (inventory actions read) :=
  le_antisymm (kernel_le_observer_kernel _ _)
    (invariant_submodule_le_kernel _ _ _ le_rfl (kernel_invariant actions read primary))

theorem common_invariant_is_retained (submodule : Submodule R C)
    (invisible : submodule ≤ LinearMap.ker read)
    (closed : ∀ letter, submodule ≤ submodule.comap (actions letter)) :
    submodule ≤ LinearMap.ker (inventory actions read) := by
  intro value member
  change inventory actions read value = 0
  funext word
  apply invisible
  have remains (word : List I) (point : C) (inside : point ∈ submodule) : run actions word point ∈ submodule := by
    induction word generalizing point with
    | nil => exact inside
    | cons letter rest previous => exact previous (actions letter point) (closed letter inside)
  exact remains word value member

end
end SourceGeneratedActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
