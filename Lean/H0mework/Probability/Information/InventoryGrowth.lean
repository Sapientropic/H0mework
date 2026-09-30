import H0mework.Probability.Information.InventorySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceUniformFibreVariance
open scoped Classical
noncomputable section

variable {Observed : Type*} [DecidableEq Observed]

theorem outputs_append (bound : Nat) (read : Nat → Observed) :
    outputs (bound + 1) (fun actor => read actor.val) =
      insert (read (bound + 1)) (outputs bound (fun actor => read actor.val)) := by
  classical
  ext value
  simp only [outputs, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨actor, same⟩
    cases actor using Fin.lastCases with
    | last => exact Or.inl same.symm
    | cast actor => exact Or.inr ⟨actor, same⟩
  · rintro (same | ⟨actor, same⟩)
    · exact ⟨Fin.last (bound + 1), same.symm⟩
    · exact ⟨actor.castSucc, same⟩

variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem cost_append (bound : Nat) (read : Nat → Observed) :
    cost (bound + 1) (fun actor => read actor.val) =
      cost bound (fun actor => read actor.val) +
        if read (bound + 1) ∈ outputs bound (fun actor => read actor.val) then 1 else 0 := by
  rw [cost_eq, cost_eq, outputs_append]
  by_cases old : read (bound + 1) ∈ outputs bound (fun actor => read actor.val)
  · rw [if_pos old, Finset.card_insert_of_mem old]
    push_cast
    ring
  · rw [if_neg old, Finset.card_insert_of_notMem old]
    push_cast
    ring

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
