import H0mework.Fock.RetainedCoarsening.Equality

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (At next)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

theorem outside_source (runtime : LivingRuntimeState process) (frame : At runtime Fine) (read : Nat → Fine)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (key : Fine) (absent : key ∉ frame.keys) : (frame.native key).1 = 0 := by
  rw [source, SourceReceivedConditionalMerge.outside_row read (inventoryBound runtime) key (by rwa [← keys])]

theorem native_next (runtime : LivingRuntimeState process) (frame : At runtime Fine) (read : Nat → Fine) (forget : Fine → Coarse)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) :
    (merge (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
        (next runtime frame (read runtime.tick.next.state)) forget).native =
      (next runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget)
        (forget (read runtime.tick.next.state))).native := by
  have afterKeys : (next runtime frame (read runtime.tick.next.state)).keys =
      SourceUniformFibreVariance.outputs (inventoryBound runtime.tick.next) (fun actor => read actor.val) := by
    rw [next_keys, keys]
    exact SourceReceivedKeyInventory.keys_next runtime read
  rw [native_source _ _ _ read forget (SourceRetainedReceiver.next_native runtime frame read source) afterKeys]
  exact (SourceRetainedReceiver.next_native runtime _ (forget ∘ read)
    (native_source _ _ frame read forget source keys)).symm

theorem merge_next (runtime : LivingRuntimeState process) (frame : At runtime Fine) (read : Nat → Fine) (forget : Fine → Coarse)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) :
    merge (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
        (next runtime frame (read runtime.tick.next.state)) forget =
      next runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget)
        (forget (read runtime.tick.next.state)) := by
  apply frame_value_ext
  · change ((next runtime frame (read runtime.tick.next.state)).keys.image forget) = _
    rw [next_keys, next_keys, Finset.image_insert]
    rfl
  · exact native_next runtime frame read forget source keys
  · intro coarse
    exact merged_next_value runtime frame forget _ coarse (outside_source runtime frame read source keys)

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
