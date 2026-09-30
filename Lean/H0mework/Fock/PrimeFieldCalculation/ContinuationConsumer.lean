import H0mework.Fock.PrimeFieldCalculation.ContinuationMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionContinuation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourcePrimeHistoryRecovery SourceGeneratedActionWords
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

local instance fieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)

theorem source_word_birth (runtime : LivingRuntimeState process)
    (actor : Fin (inventoryBound runtime + 1)) :
    Recorded.sourceWord (inventoryBound runtime) (record runtime actor) =
      ∑ index : Fin (inventoryBound runtime + 1),
        SourcePrimeCalculation.birthCoefficient (inventoryBound runtime) index actor •
          sourceAction nativeStep (sourcePoint ((runtimeAt index.val).current.visit.current : Current)) := by
  rw [record_original]
  exact Recorded.sourceWord_actual_birth _ actor

theorem conditional_birth (runtime : LivingRuntimeState process)
    (index candidate : Fin (inventoryBound runtime + 1)) :
    ((SourceGeneratedActionObservationHistory.FiniteRecurrence.Native.conditional (process := process)
        rawField (windowBound sourceOwner (inventoryBound runtime)) runtimeSeed (inventoryBound runtime) index candidate).toReal : ℂ) =
      (coefficient sourceOwner (inventoryBound runtime) candidate (record runtime index) : ℂ) := by
  rw [record_original, SourcePrimeCalculation.recorded_coefficient_is_birth]
  exact SourcePrimeCalculation.conditional_weight_is_birth _ index candidate

theorem original_record_transfer (runtime : LivingRuntimeState process) (depth : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
      CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime))
    (actor : Fin (inventoryBound runtime + 1)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
          CanonicalUnitArithmeticRoot.initialCurrent (inventoryBound runtime)) value
        (Recorded.whole depth (inventoryBound runtime) (record runtime actor)) =
      decoder sourceOwner (inventoryBound runtime)
        (fun index => value (Actor.originalRead depth (inventoryBound runtime) index)) (record runtime actor) := by
  rw [record_original]
  exact Recorded.original_field_transfer_on_record depth _ value actor

theorem prime_record_transfer (runtime : LivingRuntimeState process)
    (task : Fin (inventoryBound runtime + 1) → ℂ) (actor : Fin (inventoryBound runtime + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed (inventoryBound runtime)
        (SourceWeightedRecovery.Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed
          (inventoryBound runtime) (taskValue (historyPMF (inventoryBound runtime)) task))
        (SourceConditionalTransfer.nextAtom (process := process) rawField runtimeSeed (inventoryBound runtime) actor) =
      decoder sourceOwner (inventoryBound runtime) task (record runtime actor) := by
  rw [record_original]
  exact Recorded.prime_transfer_on_record _ task actor

theorem acquired_source (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceGeneratedActionWords.run (Fock.Complete.action depth)
        (List.replicate (windowBound sourceOwner (inventoryBound runtime)) (.inl ()))
        ((originalField depth).symm
          (Recorded.whole depth (inventoryBound runtime) (record runtime (Fin.last (inventoryBound runtime))))) =
      Fock.Complete.point depth ((normal runtime).targetRuntime.current.visit.current : Current) := by
  rw [record_original, target_is_original]
  exact Recorded.whole_at_acquisition_normal depth _

theorem recovered_next (runtime : LivingRuntimeState process) (depth : Nat) :
    Fock.Complete.action depth (.inl ())
        (SourceGeneratedActionWords.run (Fock.Complete.action depth)
          (List.replicate (windowBound sourceOwner (inventoryBound runtime)) (.inl ()))
          ((originalField depth).symm
            (Recorded.whole depth (inventoryBound runtime) (record runtime (Fin.last (inventoryBound runtime)))))) =
      Fock.Complete.point depth ((normal runtime).targetRuntime.tick.next.current.visit.current : Current) := by
  rw [acquired_source runtime depth]
  exact Fock.Complete.action_point depth (.inl ()) ((normal runtime).targetRuntime.current.visit.current : Current)

theorem next_inventory (runtime : LivingRuntimeState process) :
    inventoryBound (normal runtime).targetRuntime.tick.next =
      completionDepth sourceOwner (inventoryBound runtime) + 2 := by
  rw [target_is_original, SourcePrimeCalculation.target_is_original]
  change inventoryBound (runtimeAt (completionDepth sourceOwner (inventoryBound runtime) + 1 + 1)) = _
  rw [inventory_bound, runtimeAt_state]

theorem round_inventory_grows (round : Nat) :
    inventoryBound (roundRuntime round) < inventoryBound (roundRuntime (round + 1)) := by
  rw [round_next, next_inventory]
  unfold completionDepth
  omega

theorem acquisition_consumed (runtime : LivingRuntimeState process) :
    let bound := inventoryBound runtime
    let depth := completionDepth sourceOwner bound + 2
    Fintype.card (SourceOwnedObservationHistory.FamilyModel.Fock.Index runtime.state) = bound + 1 ∧
      (priorHistory runtime).target = runtime ∧
      type_of% (material_budget runtime) ∧
      (∀ index : Fin (bound), type_of% (material_prefix runtime index)) ∧
      (∀ index : Fin (completionDepth sourceOwner bound + 1),
        type_of% (material_original runtime index) ∧
        type_of% (material runtime index).factorizes ∧
        (∀ new : ¬ index.val < bound, type_of% (material_suffix runtime index new))) ∧
      (∀ index : Fin ((frontier runtime).stageCount + 1),
        (frontier runtime).LocalOperationAt index (frontier runtime).sourcePayload
          ((frontier runtime).history.stageAt index)) ∧
      (∀ actor : Fin (bound + 1), type_of% (record_original runtime actor) ∧
        type_of% (source_word_birth runtime actor)) ∧
      (∀ index candidate : Fin (bound + 1), type_of% (conditional_birth runtime index candidate)) ∧
      (∀ value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
          CanonicalUnitArithmeticRoot.initialCurrent bound,
        ∀ actor : Fin (bound + 1), type_of% (original_record_transfer runtime depth value actor)) ∧
      (∀ task : Fin (bound + 1) → ℂ, ∀ actor : Fin (bound + 1), type_of% (prime_record_transfer runtime task actor)) ∧
      type_of% (SourceGeneratedRecordFrame.recorded_family_consumed bound) ∧
      type_of% (acquired_source runtime depth) ∧ type_of% (recovered_next runtime depth) ∧
      type_of% (target_is_original runtime) ∧ type_of% (normal runtime).target_factorizes ∧
      type_of% (coversAt_factorizes (normal runtime).targetRuntime .particleWave) ∧
      type_of% (next_inventory runtime) := by
  dsimp only
  refine ⟨?_, prefix_target runtime, material_budget runtime, material_prefix runtime,
    (fun index => ⟨material_original runtime index, (material runtime index).factorizes,
      material_suffix runtime index⟩), (realization runtime).operationAt,
    (fun actor => ⟨record_original runtime actor, source_word_birth runtime actor⟩), conditional_birth runtime,
    original_record_transfer runtime _, prime_record_transfer runtime,
    SourceGeneratedRecordFrame.recorded_family_consumed _, acquired_source runtime _, recovered_next runtime _,
    target_is_original runtime, (normal runtime).target_factorizes,
    coversAt_factorizes (normal runtime).targetRuntime .particleWave, next_inventory runtime⟩
  simp only [FamilyModel.Fock.Index, Fintype.card_fin, runtime_bound, inventory_bound]

theorem round_consumed (round : Nat) :
    type_of% (acquisition_consumed (roundRuntime round)) ∧
      type_of% (round_next round) ∧ type_of% (round_inventory_grows round) ∧
      (priorHistory (roundRuntime (round + 1))).target =
        (normal (roundRuntime round)).targetRuntime.tick.next :=
  ⟨acquisition_consumed (roundRuntime round), round_next round, round_inventory_grows round,
    (prefix_target (roundRuntime (round + 1))).trans (round_next round)⟩

end
end SourceGeneratedAcquisitionContinuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
