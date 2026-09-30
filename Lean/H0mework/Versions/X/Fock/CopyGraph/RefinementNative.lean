import H0mework.Versions.X.Fock.CopyGraph.RefinementComplete
import H0mework.Versions.X.Fock.CopyGraph.RefinementField
import H0mework.Versions.X.Fock.CopyGraph.CostObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourcePrimeHistoryRecovery
open SourceGeneratedJointClockGraph SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance nativePrefixMeasurable (width : Nat) : MeasurableSpace (SourceFixedInventoryRecovery.Observation width) := ⊤

theorem complete_field_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : FieldSpace (inventoryBound runtime) (inventoryBound runtime)) :
    SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (SourceFixedInventoryRecovery.query runtime (windowBound sourceOwner (inventoryBound runtime)))
      (SourceCopyGraph.action (inventoryBound runtime) index (fieldRead (inventoryBound runtime) (inventoryBound runtime) value)) = value := by
  let depth := inventoryBound runtime
  let query := SourceFixedInventoryRecovery.query runtime (windowBound sourceOwner depth)
  let task := Actor.currentPullback depth depth value
  have restored := IsometricRetainedTransfer.pullback_transfer_add_residual (pullback (historyPMF depth) query) task
  rw [complete_weighted_residual runtime, add_zero] at restored
  have source := congrArg (SourceConditionalGraph.copyRead depth depth index) restored
  rw [← SourceConditionalGraphDecoder.action_source] at source
  have decoded := congrArg (SourceConditionalGraphDecoder.decode depth depth index query) source
  rw [SourceConditionalGraphDecoder.decode_action] at decoded
  change Actor.currentTransfer depth depth (pullback (historyPMF depth) query
    (SourceConditionalGraphDecoder.decode depth depth index query (SourceConditionalGraph.copyRead depth depth index task))) = value
  rw [← decoded, restored]
  exact IsometricRetainedTransfer.transfer_pullback (Actor.currentPullback depth depth) value

def PrefixAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    (∀ width : Fin (windowBound sourceOwner depth),
      (∀ value : SourceJointClockGraph.Carrier,
        type_of% (prefix_residual_update runtime index width.val value) ∧ type_of% (prefix_energy runtime index width.val value)) ∧
      (∀ actor : Fin (depth + 1), type_of% (SourceFixedInventoryRecovery.query_tail_birth runtime width.val actor)) ∧
      ∀ actor : Fin (depth + 1), ∀ time : Fin (width.val + 2),
        type_of% (SourceFixedInventoryRecovery.query_actual_material runtime (width.val + 1) (Nat.succ_le_of_lt width.isLt) actor time)) ∧
    (∀ value : Space (historyPMF depth), type_of% (complete_residual runtime index value) ∧ type_of% (full_gain_budget runtime index value)) ∧
    (∀ value : FieldSpace depth depth, type_of% (complete_field_recovery runtime index value)) ∧
    type_of% (SourceFixedInventoryRecovery.complete_record runtime) ∧
    type_of% (SourceFixedInventoryRecovery.sourceGeneratedFixedInventoryRecovery runtime) ∧
    type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave)

theorem prefix_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : PrefixAt runtime index := by
  dsimp only [PrefixAt]
  with_reducible exact ⟨(fun width => ⟨(fun value => ⟨prefix_residual_update runtime index width.val value, prefix_energy runtime index width.val value⟩),
    SourceFixedInventoryRecovery.query_tail_birth runtime width.val,
    SourceFixedInventoryRecovery.query_actual_material runtime (width.val + 1) (Nat.succ_le_of_lt width.isLt)⟩),
    (fun value => ⟨complete_residual runtime index value, full_gain_budget runtime index value⟩),
    complete_field_recovery runtime index, SourceFixedInventoryRecovery.complete_record runtime,
    SourceFixedInventoryRecovery.sourceGeneratedFixedInventoryRecovery runtime,
    coversAt_factorizes runtime .particleWave, coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave⟩

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
