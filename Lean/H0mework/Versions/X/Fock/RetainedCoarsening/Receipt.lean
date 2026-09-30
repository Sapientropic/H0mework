import H0mework.Versions.X.Fock.RetainedCoarsening.Moment

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (Frame At next value)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Key : Type*} [DecidableEq Key]
noncomputable section

theorem next_keys (runtime : LivingRuntimeState process) (frame : At runtime Key) (added : Key) :
    (next runtime frame added).keys = insert added frame.keys := by
  rw [next, SourceRetainedReceiver.reindex_keys]
  rfl

theorem next_count (runtime : LivingRuntimeState process) (frame : At runtime Key) (added key : Key) :
    ((next runtime frame added).native key).1 =
      if key = added then (frame.native key).1 + 1 else (frame.native key).1 := by
  have transport (left right : Nat) (same : left = right) (state : SourceConditionalNativeObservers.State Key left) :
      ((cast (congrArg (SourceConditionalNativeObservers.State Key) same) state) key).1 = (state key).1 := by
    cases same
    rfl
  rw [next, SourceRetainedReceiver.reindex_native, transport _ _ (SourceActualImageStep.next_bound runtime).symm]
  change (SourceConditionalNativeObservers.advance (fun _ => added) (inventoryBound runtime) frame.native key).1 = _
  by_cases selected : key = added <;> simp only [SourceConditionalNativeObservers.advance, selected, ↓reduceIte]

theorem counted_next_value (runtime : LivingRuntimeState process) (frame : At runtime Key) (added key : Key) :
    (((next runtime frame added).native key).1 : ℂ) • value runtime.tick.next (next runtime frame added) key =
      ((frame.native key).1 : ℂ) • value runtime frame key +
        if key = added then SourceConditionalInventory.born (inventoryBound runtime) else 0 := by
  rw [next_count, SourceRetainedReceiver.next_value]
  by_cases selected : key = added
  · simp only [if_pos selected, Rat.cast_natCast, smul_add, smul_smul]
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)), one_smul]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel
  · simp only [if_neg selected, add_zero]

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
