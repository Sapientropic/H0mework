import H0mework.Fock.HistoryConditional.NativeMergeSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeMerge

open SourceConditionalNativeObservers (generate)
open SourceUniformFibreVariance (outputs fibre fibre_mem)
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem count_generated (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) (value : Coarse) :
    count read forget bound (generate read bound) value = (generate (forget ∘ read) bound value).1 := by
  have row (key : Fine) :
      (if forget key = value then (generate read bound key).1 else 0) =
        ∑ index ∈ fibre bound (fun actor => read actor.val) key,
          if forget (read index.val) = value then (1 : Nat) else 0 := by
    rw [SourceConditionalNativePosterior.count_fibre]
    have same : (∑ index ∈ fibre bound (fun actor => read actor.val) key,
        if forget (read index.val) = value then (1 : Nat) else 0) =
        ∑ _index ∈ fibre bound (fun actor => read actor.val) key, if forget key = value then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro index inside
      rw [(fibre_mem _ _ _ _).mp inside]
    rw [same]
    by_cases selected : forget key = value <;> simp [selected]
  rw [count, inventoryCount, SourceConditionalNativePosterior.count_sum]
  simp_rw [row]
  have paid := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin (bound + 1)))) (t := outputs bound (fun actor => read actor.val))
    (g := fun actor => read actor.val)
    (fun actor _ => Finset.mem_image.mpr ⟨actor, Finset.mem_univ _, rfl⟩)
    (fun actor => if forget (read actor.val) = value then (1 : Nat) else 0)
  simpa only [fibre, Function.comp_apply] using paid

end SourceConditionalNativeMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
