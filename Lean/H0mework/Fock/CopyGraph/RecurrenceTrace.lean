import H0mework.Fock.CopyGraph.RecurrenceField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance traceRecurrenceMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem loss_rank (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) :
    Module.finrank ℂ (lossMap runtime index steps).range =
      Module.finrank ℂ (SourceGraphFibreUpdate.sourceUpdate (inventoryBound runtime + steps)
        (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
        (SourceGraphGrowth.sourceRead (inventoryBound runtime) index)).range :=
  congrArg (fun update : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier => Module.finrank ℂ update.range)
    (loss_map_canonical runtime index steps)

theorem normal_account (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    let material := NativeCopy.Fock.material (inventoryBound runtime) index
    SourceCopyInventory.inventoryCost material (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime.state =
      SourceCopyInventory.inventoryCost material runtime.state +
        ∑ stage ∈ Finset.range ((frontier runtime).stageCount + 1), (Module.finrank ℂ (lossMap runtime index stage).range : ℝ) := by
  simp_rw [loss_rank]
  exact SourceGraphFibreUpdate.source_normal_account runtime index

theorem next_account (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    let material := NativeCopy.Fock.material (inventoryBound runtime) index
    SourceCopyInventory.inventoryCost material (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime.tick.next.state =
      SourceCopyInventory.inventoryCost material runtime.state +
        ∑ stage ∈ Finset.range ((frontier runtime).stageCount + 2), (Module.finrank ℂ (lossMap runtime index stage).range : ℝ) := by
  simp_rw [loss_rank]
  exact SourceGraphFibreUpdate.source_next_account runtime index

theorem normal_depth (runtime : LivingRuntimeState process) :
    inventoryBound (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime =
      inventoryBound runtime + ((frontier runtime).stageCount + 1) :=
  advance_depth runtime ((frontier runtime).stageCount + 1)

theorem next_depth (runtime : LivingRuntimeState process) :
    inventoryBound (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime.tick.next =
      inventoryBound runtime + ((frontier runtime).stageCount + 2) :=
  advance_depth runtime ((frontier runtime).stageCount + 2)

theorem normal_history_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% ((SourceGeneratedAcquisitionContinuation.normal runtime).target_factorizes) ∧
      type_of% (normal_depth runtime) ∧ type_of% (next_depth runtime) ∧
      type_of% (normal_account runtime index) ∧ type_of% (next_account runtime index) ∧
      (∀ value : SourceJointClockGraph.Carrier,
        type_of% (history_residual runtime index ((frontier runtime).stageCount + 1) value) ∧
        type_of% (history_energy runtime index ((frontier runtime).stageCount + 1) value) ∧
        type_of% (history_residual runtime index ((frontier runtime).stageCount + 2) value) ∧
        type_of% (history_energy runtime index ((frontier runtime).stageCount + 2) value)) ∧
      type_of% (stage_recovery runtime index ((frontier runtime).stageCount + 1)) ∧
      type_of% (coversAt_factorizes (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime.tick.next .particleWave) := by
  with_reducible exact ⟨(SourceGeneratedAcquisitionContinuation.normal runtime).target_factorizes,
    normal_depth runtime, next_depth runtime, normal_account runtime index, next_account runtime index,
    fun value => ⟨history_residual runtime index _ value, history_energy runtime index _ value,
      history_residual runtime index _ value, history_energy runtime index _ value⟩,
    stage_recovery runtime index _, coversAt_factorizes _ .particleWave⟩

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
