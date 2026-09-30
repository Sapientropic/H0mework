import H0mework.Fock.ReceivedStep.ActionData

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceCopyRecordedRecurrence (cutoff)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem current_extent (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (inventoryBound runtime + 1) * (index.val + 1) = cutoff runtime index 0 + 1 :=
  ((SourceCopyProgram.index_exact (inventoryBound runtime) index (inventoryBound runtime)).trans
    (by rw [SourceCopyProgram.scale_source])).symm

theorem next_extent (runtime : LivingRuntimeState process) :
    (inventoryBound runtime + 2) * ((maximumIndex runtime.tick.next).val + 1) =
      cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1 := by
  have actual := current_extent runtime.tick.next (maximumIndex runtime.tick.next)
  have source := congrArg (fun bound => (bound + 1) * ((maximumIndex runtime.tick.next).val + 1))
    (SourceActualImageStep.next_bound runtime)
  exact source.symm.trans actual

theorem capacity_grows (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (inventoryBound runtime + 1) * (index.val + 1) ≤
      (inventoryBound runtime + 2) * ((maximumIndex runtime.tick.next).val + 1) := by
  rw [current_extent, next_extent]
  have included := SourceCopyCurrentCoordinates.cutoff_le_maximum runtime index 0
  have grown := SourceCopySharedNext.cutoff_growth runtime
  omega

theorem birth_included (runtime : LivingRuntimeState process) :
    inventoryBound runtime + 2 < (inventoryBound runtime + 2) * ((maximumIndex runtime.tick.next).val + 1) := by
  rw [next_extent]
  have grown := SourceCopySharedNext.cutoff_growth runtime
  omega

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
