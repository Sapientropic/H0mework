import H0mework.Versions.X.Fock.PrimeFieldCalculation.InventoryField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedConditionalInventory

open SourceConditionalInventory SourceUniformFibreVariance SourceGeneratedRuntimeHistoryProbability
open SourceWeightedRecovery SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
noncomputable section

local instance : MeasurableSpace IntegralOneParticle := ⊤

private abbrev rawRead (bound : Nat) : Fin (bound + 1) → IntegralOneParticle := fun index => rawField index.val

theorem original_reconstruct (depth bound : Nat) (value : FieldSpace depth bound) :
    Actor.currentTransfer depth bound
        (SourceWeightedRecovery.pullback (historyPMF bound) (rawRead bound)
          (SourceWeightedRecovery.transfer (historyPMF bound) (rawRead bound) (Actor.currentPullback depth bound value))) +
      Actor.currentTransfer depth bound
        (SourceWeightedRecovery.residual (historyPMF bound) (rawRead bound) (Actor.currentPullback depth bound value)) = value := by
  have generated := congrArg (Actor.currentTransfer depth bound)
    (IsometricRetainedTransfer.pullback_transfer_add_residual
      (SourceWeightedRecovery.pullback (historyPMF bound) (rawRead bound)) (Actor.currentPullback depth bound value))
  rw [map_add] at generated
  exact generated.trans (IsometricRetainedTransfer.transfer_pullback (Actor.currentPullback depth bound) value)

theorem original_energy (depth bound : Nat) (value : FieldSpace depth bound) :
    ‖value‖ ^ 2 =
      ‖SourceWeightedRecovery.transfer (historyPMF bound) (rawRead bound) (Actor.currentPullback depth bound value)‖ ^ 2 +
        ‖Actor.currentTransfer depth bound
          (SourceWeightedRecovery.residual (historyPMF bound) (rawRead bound) (Actor.currentPullback depth bound value))‖ ^ 2 := by
  rw [actor_transfer_norm]
  have generated := IsometricRetainedTransfer.energy_decomposition
    (SourceWeightedRecovery.pullback (historyPMF bound) (rawRead bound)) (Actor.currentPullback depth bound value)
  simpa only [(Actor.currentPullback depth bound).norm_map] using generated

theorem original_inventory_cost (depth bound : Nat) :
    (∑ actor : Fin (bound + 1), ‖Actor.currentTransfer depth bound
      (SourceWeightedRecovery.residual (historyPMF bound) (rawRead bound)
        (taskValue (historyPMF bound) (fun index => (unitTask bound actor index : ℂ))))‖ ^ 2) = snapshotCost bound := by
  simp_rw [actor_transfer_norm]
  rfl

theorem original_unit_norm (depth bound : Nat) (actor : Fin (bound + 1)) :
    ‖Actor.currentTransfer depth bound
      (taskValue (historyPMF bound) (fun index => (unitTask bound actor index : ℂ)))‖ = 1 := by
  rw [actor_transfer_norm, unit_norm]

theorem full_record_read (runtime : LivingRuntimeState process) (depth : Nat)
    (value : SourceWeightedRecovery.Space (historyPMF (inventoryBound runtime)))
    (index : Fin (inventoryBound runtime + 1)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
          CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime))
        (Actor.currentTransfer depth (inventoryBound runtime) value)
        (Recorded.whole depth (inventoryBound runtime) (record runtime index)) = value index := by
  rw [record_original]
  change SourceGeneratedAtomicObservation.Recorded.query depth (inventoryBound runtime) index
    (Actor.currentTransfer depth (inventoryBound runtime) value) = value index
  rw [SourceGeneratedRecordFrame.query_sample]
  exact (Actor.currentPullback_at depth (inventoryBound runtime)
    (Actor.currentTransfer depth (inventoryBound runtime) value) index).symm.trans
      (congrArg (fun task : SourceWeightedRecovery.Space (historyPMF (inventoryBound runtime)) => task index)
        (actor_transfer_samples depth (inventoryBound runtime) value))

theorem full_record_cost_zero (runtime : LivingRuntimeState process) (depth : Nat) :
    (∑ actor : Fin (inventoryBound runtime + 1),
      error (historyPMF (inventoryBound runtime)) (record runtime)
        (fun index => (unitTask (inventoryBound runtime) actor index : ℂ))
        (fun samples => IsometricRetainedTransfer.transfer
          (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
            CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime))
          (Actor.currentTransfer depth (inventoryBound runtime)
            (taskValue (historyPMF (inventoryBound runtime)) (fun index => (unitTask (inventoryBound runtime) actor index : ℂ))))
          (Recorded.whole depth (inventoryBound runtime) samples))) = 0 := by
  simp only [error, full_record_read, taskValue_at _ _ _ (source_positive _ _), sub_self,
    norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

end
end SourceGeneratedConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
