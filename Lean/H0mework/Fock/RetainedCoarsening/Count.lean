import H0mework.Fock.RetainedCoarsening.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (At next)
open SourceGeneratedAcquisitionContinuation
open SourceConditionalNativeMerge (inventoryCount)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

theorem count_next (runtime : LivingRuntimeState process) (frame : At runtime Fine) (forget : Fine → Coarse)
    (added : Fine) (coarse : Coarse)
    (outside : ∀ key, key ∉ frame.keys → (frame.native key).1 = 0) :
    inventoryCount (next runtime frame added).keys forget (inventoryBound runtime.tick.next)
        (next runtime frame added).native coarse = inventoryCount frame.keys forget (inventoryBound runtime) frame.native coarse +
      if forget added = coarse then 1 else 0 := by
  have term (key : Fine) :
      (if forget key = coarse then ((next runtime frame added).native key).1 else 0) =
        (if forget key = coarse then (frame.native key).1 else 0) +
        (if key = added then (if forget added = coarse then 1 else 0) else 0) := by
    rw [next_count]
    by_cases same : key = added
    · subst key
      by_cases selected : forget added = coarse <;> simp only [selected, ↓reduceIte, add_zero]
    · by_cases selected : forget key = coarse <;> simp only [if_neg same, selected, ↓reduceIte, add_zero]
  dsimp only [inventoryCount]
  rw [next_keys]
  simp only [term, Finset.sum_add_distrib]
  have old : (∑ key ∈ insert added frame.keys, if forget key = coarse then (frame.native key).1 else 0) =
      ∑ key ∈ frame.keys, if forget key = coarse then (frame.native key).1 else 0 := by
    by_cases present : added ∈ frame.keys
    · rw [Finset.insert_eq_of_mem present]
    · rw [Finset.sum_insert present, outside added present, ite_self, zero_add]
  rw [old]
  congr 1
  rw [Finset.sum_eq_single added]
  · exact if_pos rfl
  · intro key _ different
    exact if_neg different
  · intro absent
    exact (absent (Finset.mem_insert_self _ _)).elim

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
