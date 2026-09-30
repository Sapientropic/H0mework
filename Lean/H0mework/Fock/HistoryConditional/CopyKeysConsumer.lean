import H0mework.Fock.HistoryConditional.CopyKeysPosterior
import H0mework.Fock.HistoryConditional.CopyBirthMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeKeys

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open SourceOwnedObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

theorem generated_original (depth bound : Nat) (index : SourceCopyObservation.Index depth) (actor : Fin (bound + 1)) :
    SourceConditionalNativeObservers.generate (jointKey index.val) bound (jointKey index.val actor.val) =
      SourceConditionalNativeObservers.generate (SourceCopyInventory.read (NativeCopy.Fock.material depth index)) bound
        (SourceCopyInventory.read (NativeCopy.Fock.material depth index) actor.val) := by
  have counts :
      (SourceConditionalNativeObservers.generate (jointKey index.val) bound (jointKey index.val actor.val)).1 =
      (SourceConditionalNativeObservers.generate (SourceCopyInventory.read (NativeCopy.Fock.material depth index)) bound
        (SourceCopyInventory.read (NativeCopy.Fock.material depth index) actor.val)).1 := by
    rw [SourceConditionalNativePosterior.count_sum, SourceConditionalNativePosterior.count_sum]
    apply Finset.sum_congr rfl
    intro candidate _
    have same := joint_fibre depth index candidate.val actor.val
    by_cases native : jointKey index.val candidate.val = jointKey index.val actor.val
    · rw [if_pos native, if_pos (same.mp native)]
    · rw [if_neg native, if_neg (fun equal => native (same.mpr equal))]
  apply Prod.ext counts
  funext candidate
  rw [SourceConditionalNativePosterior.weight_fibre, SourceConditionalNativePosterior.weight_fibre,
    counts]
  have same := joint_fibre depth index candidate.val actor.val
  by_cases native : jointKey index.val candidate.val = jointKey index.val actor.val
  · rw [if_pos native, if_pos (same.mp native)]
  · rw [if_neg native, if_neg (fun equal => native (same.mpr equal))]

theorem updated_model (runtime : LivingRuntimeState process) (depth : Nat) (index : SourceCopyObservation.Index depth)
    (actor : Actors runtime.tick.next) :
    SourceConditionalNativeBirth.update runtime (jointKey index.val) (jointKey index.val actor.val) =
      SourceConditionalModelUpdate.modelDecoder runtime.tick.next (SourceCopyObservation.joint depth (inventoryBound runtime.tick.next) index)
        (SourceCopyObservation.joint depth (inventoryBound runtime.tick.next) index actor) := by
  rw [SourceConditionalNativeBirth.update_is_next, model_original]

theorem native_total (runtime : LivingRuntimeState process) (depth : Nat) (index : SourceCopyObservation.Index depth) :
    SourceConditionalNativeBirth.total runtime (jointKey index.val) =
      SourceConditionalNativeBirth.total runtime (SourceCopyInventory.read (NativeCopy.Fock.material depth index)) := by
  simp only [SourceConditionalNativeBirth.total, SourceConditionalNativePosterior.decoder,
    SourceConditionalNativePosterior.model, generated_original]

theorem information_original (runtime : LivingRuntimeState process) (depth : Nat) (index : SourceCopyObservation.Index depth) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (fun actor : Actors runtime => jointKey index.val actor.val) (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) =
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (SourceCopyObservation.joint depth (inventoryBound runtime) index) (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) := by
  apply SourceConditionalNext.conditionalEntropy_eq_of_kernel
  exact original_fibre depth (inventoryBound runtime) index

theorem joint_error_next (runtime : LivingRuntimeState process)
    (index : SourceCopyObservation.Index (inventoryBound runtime)) :
    SourceConditionalNativeBirth.total runtime.tick.next
      (SourceCopyInventory.read (NativeCopy.Fock.material (inventoryBound runtime) index)) =
      SourceConditionalNativeBirth.total runtime
        (SourceCopyInventory.read (NativeCopy.Fock.material (inventoryBound runtime) index)) +
          SourceConditionalNativeBirth.innovation runtime (jointKey index.val) := by
  rw [← native_total runtime.tick.next (inventoryBound runtime) index, ← native_total runtime (inventoryBound runtime) index]
  exact SourceConditionalNativeBirth.minimum_update runtime (jointKey index.val)

end
end SourceCopyNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
