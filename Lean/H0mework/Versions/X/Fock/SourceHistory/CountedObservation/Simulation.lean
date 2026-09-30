import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Table

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver (Frame Raw rawAt)
variable {Key : Type*} [DecidableEq Key]

def zeroRaw (bound stride : Nat) : Raw bound stride := (fun _ => 0, 0, 0)

structure Simulates (bound stride : Nat) (table : Table Key) (frame : Frame Key bound stride) : Prop where
  keys : ∀ key, key ∈ table ↔ key ∈ frame.keys
  rows : ∀ key, Represents bound stride (lookup table key) (frame.native key).1 (rawAt bound stride frame key)

theorem empty_represents (bound stride : Nat) : Represents bound stride emptyEntry 0 (zeroRaw bound stride) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro position
    simp [emptyEntry, coordinate]
  · simp [emptyEntry, zeroRaw]
  · simp [emptyEntry, zeroRaw]

theorem ofFrame_simulates (bound stride : Nat) (frame : Frame Key bound stride)
    (outside : ∀ key, key ∉ frame.keys → (frame.native key).1 = 0) :
    Simulates bound stride (ofFrame bound stride frame) frame := by
  refine ⟨ofFrame_keys bound stride frame, ?_⟩
  intro key
  rw [ofFrame_lookup]
  by_cases present : key ∈ frame.keys
  · rw [if_pos present]
    exact represents_encode _ _ _ _
  · rw [if_neg present, outside key present, rawAt, dif_neg present]
    exact empty_represents bound stride

theorem step_simulates (bound stride nextStride : Nat) (table : Table Key) (frame : Frame Key bound stride)
    (source : Simulates bound stride table frame) (added : Key)
    (growth : (bound + 1) * (stride + 1) ≤ (bound + 2) * (nextStride + 1))
    (birth : bound + 2 < (bound + 2) * (nextStride + 1)) :
    Simulates (bound + 1) nextStride (step bound table added)
      (SourceRetainedReceiver.step bound stride nextStride frame added) := by
  refine ⟨?_, ?_⟩
  · intro key
    rw [step_keys, source.keys]
    exact (Finset.mem_insert).symm
  · intro key
    rw [step_lookup, SourceRetainedReceiver.step_raw]
    change Represents _ _ _ (SourceConditionalNativeObservers.advance (fun _ => added) bound frame.native key).1 _
    by_cases selected : key = added
    · simp only [if_pos selected, SourceConditionalNativeObservers.advance, decide_eq_true selected]
      exact represents_advance _ _ _ _ _ _ (source.rows key) growth birth
    · simp only [if_neg selected, SourceConditionalNativeObservers.advance, decide_eq_false selected]
      exact represents_retained _ _ _ _ _ _ (source.rows key) growth birth

theorem simulated_decode (bound stride : Nat) (table : Table Key) (frame : Frame Key bound stride)
    (source : Simulates bound stride table frame)
    (key : Key) (positive : (frame.native key).1 ≠ 0) :
    decode bound stride (lookup table key) = rawAt bound stride frame key := by
  exact represented_decode _ _ _ _ _ (source.rows key) positive

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
