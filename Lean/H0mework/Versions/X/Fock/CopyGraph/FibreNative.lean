import H0mework.Versions.X.Fock.CopyGraph.FibreField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceGraphGrowth (sourceRead oldRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance nativeFibreMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem native_prior_supported : sourceRead 2 (0 : Index 2) 3 ∈
    (observed (historyPMF 2) (oldRead 2 (sourceRead 2 (0 : Index 2)))).support := by
  have source := observed_supported (historyPMF 2) (oldRead 2 (sourceRead 2 (0 : Index 2))) (2 : Fin 3)
    (SourceUniformFibreVariance.source_positive 2 (2 : Fin 3))
  have same : oldRead 2 (sourceRead 2 (0 : Index 2)) (2 : Fin 3) = sourceRead 2 (0 : Index 2) 3 := by
    with_unfolding_all exact SourceGraphGrowth.native_unit_collision
  exact same ▸ source

theorem native_normal_nonzero : normal 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)) native_prior_supported ≠ 0 :=
  normal_ne_zero 2 (0 : Index 2) _ native_prior_supported

theorem native_novel_zero : sourceUpdate 0 (0 : Index 0) (sourceRead 0 (0 : Index 0)) = 0 := by
  rw [source_update_is_loss, ← SourceGraphLoss.update_is_loss]
  exact SourceGraphLoss.native_prime_update_zero 0 (0 : Index 0) (by decide)

theorem source_rank (depth : Nat) (index : Index depth) (read : Nat → ParentCarrier × ParentCarrier) :
    Module.finrank ℂ (sourceUpdate depth index read).range = Module.finrank ℂ (SourceGraphGrowth.forgettingLoss depth index read).range :=
  congrArg (fun update : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier => Module.finrank ℂ update.range)
    (source_update_is_loss depth index read)

theorem source_normal_account (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    let depth := inventoryBound runtime
    let material := NativeCopy.Fock.material depth index
    SourceCopyInventory.inventoryCost material (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime.state =
      SourceCopyInventory.inventoryCost material runtime.state +
        ∑ step ∈ Finset.range ((frontier runtime).stageCount + 1),
          (Module.finrank ℂ (sourceUpdate (depth + step) (SourceGraphLoss.advancedIndex depth index step) (sourceRead depth index)).range : ℝ) := by
  simp_rw [source_rank]
  exact SourceGraphLoss.normal_rank_cost runtime index

theorem source_next_account (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    let depth := inventoryBound runtime
    let material := NativeCopy.Fock.material depth index
    SourceCopyInventory.inventoryCost material (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime.tick.next.state =
      SourceCopyInventory.inventoryCost material runtime.state +
        ∑ step ∈ Finset.range ((frontier runtime).stageCount + 2),
          (Module.finrank ℂ (sourceUpdate (depth + step) (SourceGraphLoss.advancedIndex depth index step) (sourceRead depth index)).range : ℝ) := by
  simp_rw [source_rank]
  exact SourceGraphLoss.generated_next_rank_cost runtime index

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
