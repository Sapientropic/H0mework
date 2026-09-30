import H0mework.Versions.X.Fock.HistoryConditional.CopyHistorySource
import H0mework.Versions.X.Fock.HistoryConditional.CopyKeysConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_row (bound : Nat) (actor : Fin (bound + 1)) :
    SourceConditionalNativeObservers.generate (read bound) bound (read bound actor.val) =
      (1, fun candidate => if candidate = actor then 1 else 0) := by
  have fibre : SourceUniformFibreVariance.fibre bound (fun point => read bound point.val) (read bound actor.val) = {actor} := by
    apply Finset.ext
    intro candidate
    rw [SourceUniformFibreVariance.fibre_mem, Finset.mem_singleton]
    exact ⟨fun same => read_injective bound same, fun same => same ▸ rfl⟩
  have count : (SourceConditionalNativeObservers.generate (read bound) bound (read bound actor.val)).1 = 1 := by
    rw [SourceConditionalNativePosterior.count_fibre, fibre, Finset.card_singleton]
  apply Prod.ext count
  funext candidate
  rw [SourceConditionalNativePosterior.weight_fibre, count]
  have same : read bound candidate.val = read bound actor.val ↔ candidate = actor :=
    ⟨fun equality => read_injective bound equality, fun equality => equality ▸ rfl⟩
  simp only [same, Nat.cast_one, inv_one]

theorem model_recovers (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    SourceConditionalNativePosterior.model runtime (read (inventoryBound runtime)) (read (inventoryBound runtime) actor.val) =
      nextRead runtime actor := by
  rw [SourceConditionalNativePosterior.model, native_row]
  classical
  rw [Finset.sum_eq_single actor]
  · simp
  · intro other _ different
    simp only [if_neg different, Rat.cast_zero, zero_smul]
  · intro absent
    exact (absent (Finset.mem_univ actor)).elim

theorem decoder_recovers (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    SourceConditionalNativePosterior.decoder runtime (read (inventoryBound runtime)) (read (inventoryBound runtime) actor.val) =
      SourceConditionalInventory.values (inventoryBound runtime) actor := by
  rw [SourceConditionalNativePosterior.decoder, model_recovers, SourceConditionalInventory.values_original]

theorem source_step (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
      (SourceConditionalNativePosterior.model runtime (read (inventoryBound runtime)) (read (inventoryBound runtime) actor.val)) =
    SourceConditionalNativePosterior.model runtime.tick.next (read (inventoryBound runtime.tick.next))
      (read (inventoryBound runtime.tick.next) (SourceActualImageStep.advanceIndex runtime actor).val) := by
  rw [model_recovers, model_recovers]
  exact SourceActualImageStep.model_step_source runtime actor

theorem next_recovery (runtime : LivingRuntimeState process) (actor : Actors runtime.tick.next) :
    SourceConditionalNativePosterior.decoder runtime.tick.next (read (inventoryBound runtime.tick.next))
      (read (inventoryBound runtime.tick.next) actor.val) =
        SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor :=
  decoder_recovers runtime.tick.next actor

end
end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
