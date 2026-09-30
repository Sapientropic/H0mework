import H0mework.Fock.HistoryConditional.ReceivedKeyInventoryMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

abbrev Raw (bound stride : Nat) := (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ

structure Frame (Key : Type*) (bound stride : Nat) where
  keys : Finset Key
  native : SourceConditionalNativeObservers.State Key bound
  observation : {key // key ∈ keys} → Raw bound stride

variable {Key : Type*} [DecidableEq Key]

def start (bound stride : Nat) (nonunit : stride ≠ 0) (keys : Finset Key)
    (samples : {key // key ∈ keys} → SourceRationalWindowReadout.Samples bound (stride + 1)) : Frame Key bound stride where
  keys := keys
  native := SourceReceivedKeyInventory.restore bound stride nonunit keys samples
  observation := fun key => SourceRationalWindowReadout.decode bound stride (samples key)

def rawAt (bound stride : Nat) (frame : Frame Key bound stride) (key : Key) : Raw bound stride :=
  if present : key ∈ frame.keys then frame.observation ⟨key, present⟩ else 0

def step (bound stride nextStride : Nat) (frame : Frame Key bound stride) (added : Key) : Frame Key (bound + 1) nextStride where
  keys := insert added frame.keys
  native := SourceConditionalNativeObservers.advance (fun _ => added) bound frame.native
  observation := fun key => SourceReceivedConditionalStep.advanceData bound stride nextStride
    (frame.native key.val).1 (decide (key.val = added)) (rawAt bound stride frame key.val)

end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
