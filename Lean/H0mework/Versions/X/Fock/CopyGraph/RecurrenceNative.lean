import H0mework.Versions.X.Fock.CopyGraph.RecurrenceEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead sourceRead pulse)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance nativeRecurrenceMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem initial_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    residual runtime index 0 (pulse (inventoryBound runtime) index) = 0 := by
  rw [residual_canonical]
  exact SourceGraphGrowth.native_old_recovery _ index

private theorem collision_at (depth : Nat) (same : depth = 2) :
    (1 : ℝ) / 6 ≤ ‖SourceGraphGrowth.newResidual depth (0 : Index depth)
      (sourceRead depth (0 : Index depth)) (pulse depth (0 : Index depth))‖ ^ 2 := by
  subst depth
  with_reducible exact SourceGraphGrowth.native_forgotten_cost

theorem native_collision :
    (1 : ℝ) / 6 ≤ ‖residual (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))) 1
      (pulse (inventoryBound (runtimeAt 2)) (0 : Index (inventoryBound (runtimeAt 2))))‖ ^ 2 := by
  rw [residual_successor]
  have depth : inventoryBound (runtimeAt 2) = 2 := (inventory_bound _).trans (runtimeAt_state 2)
  dsimp only [Nat.add_zero, SourceGraphLoss.advancedIndex]
  with_reducible exact collision_at _ depth

theorem native_novel_step : lossMap (runtimeAt 0) (0 : Index (inventoryBound (runtimeAt 0))) 0 = 0 := by
  rw [loss_map_canonical]
  simp only [inventoryBound, Nat.add_zero, SourceGraphLoss.advancedIndex]
  exact SourceGraphFibreUpdate.native_novel_zero

theorem native_novel_recovery :
    residual (runtimeAt 0) (0 : Index (inventoryBound (runtimeAt 0))) 1
      (pulse (inventoryBound (runtimeAt 0)) (0 : Index (inventoryBound (runtimeAt 0)))) = 0 := by
  have balance := energy_step (runtimeAt 0) (0 : Index (inventoryBound (runtimeAt 0))) 0
    (pulse (inventoryBound (runtimeAt 0)) (0 : Index (inventoryBound (runtimeAt 0))))
  rw [initial_recovery, native_novel_step, zero_apply, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add] at balance
  apply norm_eq_zero.mp
  have born := sq_nonneg ‖birthMap (runtimeAt 0) (0 : Index (inventoryBound (runtimeAt 0))) 0
    (pulse (inventoryBound (runtimeAt 0)) (0 : Index (inventoryBound (runtimeAt 0))))‖
  have remaining := norm_nonneg (residual (runtimeAt 0) (0 : Index (inventoryBound (runtimeAt 0))) 1
    (pulse (inventoryBound (runtimeAt 0)) (0 : Index (inventoryBound (runtimeAt 0)))))
  nlinarith only [balance, born, remaining]

theorem actual_loss_dominates :
    let runtime := runtimeAt 2
    let index : Index (inventoryBound runtime) := 0
    let value := pulse (inventoryBound runtime) index
    ‖birthMap runtime index 0 value‖ ^ 2 < ‖lossMap runtime index 0 value‖ ^ 2 := by
  dsimp only
  have cost := native_collision
  have balance := energy_step (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))) 0
    (pulse (inventoryBound (runtimeAt 2)) (0 : Index (inventoryBound (runtimeAt 2))))
  rw [initial_recovery, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at balance
  linarith only [balance, cost]

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
