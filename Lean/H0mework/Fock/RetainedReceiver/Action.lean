import H0mework.Fock.RetainedReceiver.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]

theorem step_raw (bound stride nextStride : Nat) (frame : Frame Key bound stride) (added key : Key) :
    rawAt (bound + 1) nextStride (step bound stride nextStride frame added) key =
      SourceReceivedConditionalStep.advanceData bound stride nextStride (frame.native key).1
        (decide (key = added)) (rawAt bound stride frame key) := by
  dsimp only [rawAt, step]
  by_cases present : key ∈ insert added frame.keys
  · simp only [dif_pos present]
  · have missing : key ∉ frame.keys := fun old => present (Finset.mem_insert_of_mem old)
    have different : key ≠ added := by
      intro same
      subst key
      exact present (Finset.mem_insert_self _ _)
    simp [present, missing, different, SourceReceivedConditionalStep.advanceData,
      SourceReceivedConditionalStep.coordinateAt]
    rfl

end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
