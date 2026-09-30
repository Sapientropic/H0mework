import H0mework.Fock.PrimeFieldCalculation.ContinuationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionContinuation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourcePrimeHistoryRecovery

noncomputable section

def priorHistory (runtime : LivingRuntimeState process) :
    SourceGeneratedRuntimeMaterialHistoryAt runtimeSeed (inventoryBound runtime) :=
  .generate runtimeSeed _

theorem prefix_target (runtime : LivingRuntimeState process) :
    (priorHistory runtime).target = runtime := by
  change runtimeAt (inventoryBound runtime) = runtime
  rw [inventory_bound]
  exact (runtime_eq runtime).symm

def suffixIndex (runtime : LivingRuntimeState process)
    (index : Fin (completionDepth sourceOwner (inventoryBound runtime) + 1))
    (new : ¬ index.val < inventoryBound runtime) : Fin ((frontier runtime).stageCount + 1) :=
  ⟨index.val - inventoryBound runtime, by
    have inside := index.isLt
    change index.val - inventoryBound runtime < windowBound sourceOwner (inventoryBound runtime) + 1
    unfold completionDepth at inside
    omega⟩

theorem suffix_source (runtime : LivingRuntimeState process)
    (index : Fin (completionDepth sourceOwner (inventoryBound runtime) + 1))
    (new : ¬ index.val < inventoryBound runtime) :
    runtime.advance (suffixIndex runtime index new).val = runtimeAt index.val := by
  rw [advance_original, ← inventory_bound runtime]
  exact congrArg runtimeAt (by dsimp only [suffixIndex]; omega)

def material (runtime : LivingRuntimeState process)
    (index : Fin (completionDepth sourceOwner (inventoryBound runtime) + 1)) :
    SourceGeneratedRuntimeMaterialStageAt (runtimeAt index.val) :=
  if prior : index.val < inventoryBound runtime then
    (priorHistory runtime).stageAt ⟨index.val, prior⟩
  else
    (suffix_source runtime index prior) ▸
      (frontier runtime).history.stageAt (suffixIndex runtime index prior)

theorem material_original (runtime : LivingRuntimeState process)
    (index : Fin (completionDepth sourceOwner (inventoryBound runtime) + 1)) :
    material runtime index =
      (SourcePrimeCalculation.frontier (inventoryBound runtime)).history.stageAt index := by
  cases material runtime index
  rfl

theorem material_prefix (runtime : LivingRuntimeState process)
    (index : Fin (inventoryBound runtime)) :
    material runtime ⟨index.val, by have inside := index.isLt; unfold completionDepth; omega⟩ =
      (priorHistory runtime).stageAt index :=
  dif_pos index.isLt

theorem material_suffix (runtime : LivingRuntimeState process)
    (index : Fin (completionDepth sourceOwner (inventoryBound runtime) + 1))
    (new : ¬ index.val < inventoryBound runtime) :
    HEq (material runtime index)
      ((frontier runtime).history.stageAt (suffixIndex runtime index new)) := by
  have selected : material runtime index =
      Eq.recOn (motive := fun next _ => SourceGeneratedRuntimeMaterialStageAt next)
        (suffix_source runtime index new)
        ((frontier runtime).history.stageAt (suffixIndex runtime index new)) := dif_neg new
  exact (heq_of_eq selected).trans (eqRec_heq (suffix_source runtime index new) _)

def record (runtime : LivingRuntimeState process)
    (actor : Fin (inventoryBound runtime + 1)) : Raw sourceOwner (inventoryBound runtime) := fun time =>
  rawField (material runtime (cell sourceOwner (inventoryBound runtime) actor time)).next.state

theorem record_original (runtime : LivingRuntimeState process)
    (actor : Fin (inventoryBound runtime + 1)) :
    record runtime actor = SourcePrimeCalculation.recordedQuery (inventoryBound runtime) actor := by
  funext time
  unfold record SourcePrimeCalculation.recordedQuery
  rw [material_original]
  rfl

theorem material_budget (runtime : LivingRuntimeState process) :
    inventoryBound runtime + ((frontier runtime).stageCount + 1) =
      completionDepth sourceOwner (inventoryBound runtime) + 1 := by
  change inventoryBound runtime + (windowBound sourceOwner (inventoryBound runtime) + 1) = _
  unfold completionDepth
  omega

end
end SourceGeneratedAcquisitionContinuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
