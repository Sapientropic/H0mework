import H0mework.Fock.CopyFiniteComplete.Recorded

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourcePrimeHistoryRecovery
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] windowMeasurable

theorem normal_inventory_le_next (runtime : LivingRuntimeState process) :
    inventoryBound (normal runtime).targetRuntime ≤ inventoryBound (normal runtime).targetRuntime.tick.next := by
  rw [SourceGraphRecurrence.normal_depth, SourceGraphRecurrence.next_depth]
  omega

def nextRecord (runtime : LivingRuntimeState process) (actor : Fin (inventoryBound runtime + 1)) :
    Raw sourceOwner (inventoryBound runtime) := fun time =>
  rawField (((priorHistory (normal runtime).targetRuntime.tick.next).stageAt
    (Fin.castLE (normal_inventory_le_next runtime) (recordIndex runtime actor time))).next.state)

theorem next_record (runtime : LivingRuntimeState process) : nextRecord runtime = completedRecord runtime := rfl

theorem next_history_target (runtime : LivingRuntimeState process) :
    (priorHistory (normal runtime).targetRuntime.tick.next).target = (normal runtime).targetRuntime.tick.next :=
  prefix_target _

theorem next_material_factorizes (runtime : LivingRuntimeState process)
    (actor : Fin (inventoryBound runtime + 1))
    (time : Fin (windowBound sourceOwner (inventoryBound runtime) + 1)) :
    type_of% (((priorHistory (normal runtime).targetRuntime.tick.next).stageAt
      (Fin.castLE (normal_inventory_le_next runtime) (recordIndex runtime actor time))).factorizes) :=
  ((priorHistory (normal runtime).targetRuntime.tick.next).stageAt
    (Fin.castLE (normal_inventory_le_next runtime) (recordIndex runtime actor time))).factorizes

theorem recovery_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    recovery runtime index = SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (nextRecord runtime) := by
  rw [next_record]
  rfl

theorem last_cell_is_normal (runtime : LivingRuntimeState process) :
    completedRecord runtime (Fin.last (inventoryBound runtime)) (Fin.last (windowBound sourceOwner (inventoryBound runtime))) =
      rawField (normal runtime).targetRuntime.state := by
  rw [completed_record, ← SourceFixedInventoryRecovery.complete_record, SourceFixedInventoryRecovery.query_value]
  rw [← inventory_bound (normal runtime).targetRuntime, normal_inventory]
  unfold completionDepth
  congr 1
  simp only [Fin.val_last]
  omega

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
