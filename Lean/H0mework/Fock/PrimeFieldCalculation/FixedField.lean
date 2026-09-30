import H0mework.Fock.PrimeFieldCalculation.FixedMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFixedInventoryRecovery

open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceWeightedRecovery SourceConditionalInventory SourceGeneratedAcquisitionMeasure
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance fieldObservationMeasurable (width : Nat) : MeasurableSpace (Observation width) := ⊤

def originalRead (runtime : LivingRuntimeState process) (depth width : Nat)
    (inside : width ≤ windowBound sourceOwner (inventoryBound runtime))
    (value : Field nativeStep (rawWords depth)) : Observation width := fun time =>
  Recorded.recordedRestriction depth (inventoryBound runtime) value (Fin.castLE (Nat.succ_le_succ inside) time)

theorem originalRead_next (runtime : LivingRuntimeState process) (depth width : Nat)
    (inside : width ≤ windowBound sourceOwner (inventoryBound runtime))
    (actor : Fin (inventoryBound runtime + 1)) :
    originalRead runtime depth width inside (Actor.nextRead depth (inventoryBound runtime) actor) = query runtime width actor := by
  funext time
  unfold originalRead
  rw [Recorded.recordedRestriction_nextRead]
  exact (query_record_prefix runtime width inside actor time).trans
    (congrFun (record_original runtime actor) (Fin.castLE (Nat.succ_le_succ inside) time)) |>.symm

theorem original_decoder_lower (runtime : LivingRuntimeState process) (depth width : Nat)
    (inside : width ≤ windowBound sourceOwner (inventoryBound runtime))
    (decoder : Fin (inventoryBound runtime + 1) → Observation width → ℂ) :
    costAt runtime width ≤ ∑ actor,
      error (historyPMF (inventoryBound runtime)) (Actor.nextRead depth (inventoryBound runtime))
        (fun index => (unitTask (inventoryBound runtime) actor index : ℂ))
        (decoder actor ∘ originalRead runtime depth width inside) := by
  have generated := all_decoder_lower (inventoryBound runtime) (query runtime width) decoder
  rw [← cost_eq] at generated
  simpa only [costAt, error, Function.comp_apply, originalRead_next] using generated

theorem original_reconstruct (runtime : LivingRuntimeState process) (depth width : Nat)
    (value : FieldSpace depth (inventoryBound runtime)) :
    Actor.currentTransfer depth (inventoryBound runtime)
        (SourceWeightedRecovery.pullback (historyPMF (inventoryBound runtime)) (query runtime width)
          (SourceWeightedRecovery.transfer (historyPMF (inventoryBound runtime)) (query runtime width)
            (Actor.currentPullback depth (inventoryBound runtime) value))) +
      Actor.currentTransfer depth (inventoryBound runtime)
        (SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) (query runtime width)
          (Actor.currentPullback depth (inventoryBound runtime) value)) = value := by
  have generated := congrArg (Actor.currentTransfer depth (inventoryBound runtime))
    (IsometricRetainedTransfer.pullback_transfer_add_residual
      (SourceWeightedRecovery.pullback (historyPMF (inventoryBound runtime)) (query runtime width))
      (Actor.currentPullback depth (inventoryBound runtime) value))
  rw [map_add] at generated
  exact generated.trans (IsometricRetainedTransfer.transfer_pullback (Actor.currentPullback depth (inventoryBound runtime)) value)

theorem original_energy (runtime : LivingRuntimeState process) (depth width : Nat)
    (value : FieldSpace depth (inventoryBound runtime)) :
    ‖value‖ ^ 2 =
      ‖SourceWeightedRecovery.transfer (historyPMF (inventoryBound runtime)) (query runtime width)
        (Actor.currentPullback depth (inventoryBound runtime) value)‖ ^ 2 +
      ‖Actor.currentTransfer depth (inventoryBound runtime)
        (SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) (query runtime width)
          (Actor.currentPullback depth (inventoryBound runtime) value))‖ ^ 2 := by
  rw [actor_transfer_norm]
  have generated := IsometricRetainedTransfer.energy_decomposition
    (SourceWeightedRecovery.pullback (historyPMF (inventoryBound runtime)) (query runtime width))
    (Actor.currentPullback depth (inventoryBound runtime) value)
  simpa only [(Actor.currentPullback depth (inventoryBound runtime)).norm_map] using generated

theorem original_inventory_cost (runtime : LivingRuntimeState process) (depth width : Nat) :
    (∑ actor : Fin (inventoryBound runtime + 1),
      ‖Actor.currentTransfer depth (inventoryBound runtime)
        (SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) (query runtime width)
          (taskValue (historyPMF (inventoryBound runtime)) (fun index => (unitTask (inventoryBound runtime) actor index : ℂ))))‖ ^ 2) =
        costAt runtime width := by
  simp_rw [actor_transfer_norm]
  rfl

end
end SourceFixedInventoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
