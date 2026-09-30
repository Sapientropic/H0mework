import H0mework.Versions.X.Fock.RetainedReceiver.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (Raw Frame rawAt)
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

def weight (bound stride : Nat) (frame : Frame Fine bound stride) (forget : Fine → Coarse)
    (coarse : Coarse) (key : Fine) : ℚ :=
  if forget key = coarse then (frame.native key).1 /
    (SourceConditionalNativeMerge.inventoryCount frame.keys forget bound frame.native coarse : ℚ) else 0

def blend (bound stride : Nat) (frame : Frame Fine bound stride) (forget : Fine → Coarse)
    (coarse : Coarse) : Raw bound stride :=
  ∑ key ∈ frame.keys, weight bound stride frame forget coarse key • rawAt bound stride frame key

def merge (bound stride : Nat) (frame : Frame Fine bound stride) (forget : Fine → Coarse) : Frame Coarse bound stride where
  keys := frame.keys.image forget
  native := SourceConditionalNativeMerge.inventoryMerge frame.keys forget bound frame.native
  observation := fun key => blend bound stride frame forget key.val

theorem raw_merge (bound stride : Nat) (frame : Frame Fine bound stride) (forget : Fine → Coarse) (coarse : Coarse) :
    rawAt bound stride (merge bound stride frame forget) coarse = blend bound stride frame forget coarse := by
  dsimp only [rawAt, merge]
  split_ifs with present
  · rfl
  · symm
    apply Finset.sum_eq_zero
    intro key inside
    have different : forget key ≠ coarse := by
      intro same
      exact present (Finset.mem_image.mpr ⟨key, inside, same⟩)
    simp only [weight, if_neg different, zero_smul]

theorem native_source (bound stride : Nat) (frame : Frame Fine bound stride) (read : Nat → Fine) (forget : Fine → Coarse)
    (source : frame.native = SourceConditionalNativeObservers.generate read bound)
    (keys : frame.keys = SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) :
    (merge bound stride frame forget).native = SourceConditionalNativeObservers.generate (forget ∘ read) bound := by
  rw [merge, source, keys]
  exact SourceConditionalNativeMerge.merged_generated read forget bound

theorem keys_source (bound stride : Nat) (frame : Frame Fine bound stride) (read : Nat → Fine) (forget : Fine → Coarse)
    (keys : frame.keys = SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) :
    (merge bound stride frame forget).keys = SourceUniformFibreVariance.outputs bound (fun actor => forget (read actor.val)) := by
  rw [merge, keys]
  exact Finset.image_image

end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
