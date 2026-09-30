import H0mework.Versions.X.Fock.CopyFiniteComplete.Residual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceGeneratedAcquisitionContinuation SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem normal_inventory (runtime : LivingRuntimeState process) :
    inventoryBound (normal runtime).targetRuntime = completionDepth sourceOwner (inventoryBound runtime) + 1 :=
  (SourceGraphRecurrence.normal_depth runtime).trans (material_budget runtime)

def recordIndex (runtime : LivingRuntimeState process) (actor : Fin (inventoryBound runtime + 1))
    (time : Fin (windowBound sourceOwner (inventoryBound runtime) + 1)) :
    Fin (inventoryBound (normal runtime).targetRuntime) :=
  ⟨(cell sourceOwner (inventoryBound runtime) actor time).val, by
    rw [normal_inventory]
    exact (cell sourceOwner (inventoryBound runtime) actor time).isLt⟩

def completedRecord (runtime : LivingRuntimeState process) (actor : Fin (inventoryBound runtime + 1)) :
    Raw sourceOwner (inventoryBound runtime) := fun time =>
  rawField (((priorHistory (normal runtime).targetRuntime).stageAt (recordIndex runtime actor time)).next.state)

theorem completed_record (runtime : LivingRuntimeState process) : completedRecord runtime = record runtime := rfl

theorem completed_history_target (runtime : LivingRuntimeState process) :
    (priorHistory (normal runtime).targetRuntime).target = (normal runtime).targetRuntime :=
  prefix_target _

theorem completed_cell (runtime : LivingRuntimeState process) (actor : Fin (inventoryBound runtime + 1))
    (time : Fin (windowBound sourceOwner (inventoryBound runtime) + 1)) :
    completedRecord runtime actor time =
      rawField (material runtime (cell sourceOwner (inventoryBound runtime) actor time)).next.state := rfl

theorem completed_material_factorizes (runtime : LivingRuntimeState process)
    (actor : Fin (inventoryBound runtime + 1))
    (time : Fin (windowBound sourceOwner (inventoryBound runtime) + 1)) :
    type_of% (((priorHistory (normal runtime).targetRuntime).stageAt (recordIndex runtime actor time)).factorizes) :=
  ((priorHistory (normal runtime).targetRuntime).stageAt (recordIndex runtime actor time)).factorizes

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
