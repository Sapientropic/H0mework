import H0mework.Fock.HistoryConditional.ReceivedKeyInventoryConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedKeyInventory

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalModel (Actors fullRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧ type_of% (keys_next runtime (clockRead 0)) ∧
  ∀ (nonunit : (maximumIndex runtime).val ≠ 0)
      (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)),
    (∀ key : ℤ × ℤ, type_of% (reconstruction runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples key)) ∧
    (∀ depth : Nat, type_of% (information_cost runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples depth)) ∧
    ∀ budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
          SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
            (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
              SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
                (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2,
      type_of% (restored_source runtime nonunit (clockRead 0) samples budgets) ∧
      type_of% (restored_next runtime nonunit (clockRead 0) samples budgets) ∧
      (∀ actor : Actors runtime, type_of% (clock_recovers runtime nonunit samples actor budgets)) ∧
      (∀ actor : Actors runtime.tick.next, type_of% (clock_next_recovers runtime nonunit samples actor budgets)) ∧
      type_of% (clock_parity runtime nonunit samples budgets) ∧
      (∀ key : ℤ × ℤ, type_of% (next_residual runtime nonunit (clockRead 0) samples key budgets)) ∧
      type_of% (merged_next_source runtime nonunit (clockRead 0) SourceConditionalNativeMerge.forgetClock samples budgets) ∧
      (∀ (key : ZMod 2) (supported : key ∈ (SourceConditionalHistory.observed
          (SourceConditionalHistory.observed (historyPMF (inventoryBound runtime)) (fullRead runtime))
            SourceConditionalNativeMerge.forgetClock).support) (actor : Actors runtime),
        type_of% (full_mixture runtime nonunit samples key supported actor budgets)) ∧
      ∀ depth : Nat,
        type_of% (field_decoder_source runtime nonunit samples depth budgets) ∧
        type_of% (table_next runtime nonunit samples depth budgets) ∧
        type_of% (compression_loss runtime nonunit samples depth budgets) ∧
        ∀ enough : 2 ≤ inventoryBound runtime,
          type_of% (compression_positive runtime nonunit samples depth enough budgets)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, keys_next runtime (clockRead 0), fun nonunit samples =>
    ⟨fun key => reconstruction runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples key,
      fun depth => information_cost runtime nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples depth,
      fun budgets => ⟨restored_source runtime nonunit (clockRead 0) samples budgets,
        restored_next runtime nonunit (clockRead 0) samples budgets,
        fun actor => clock_recovers runtime nonunit samples actor budgets,
        fun actor => clock_next_recovers runtime nonunit samples actor budgets,
        clock_parity runtime nonunit samples budgets,
        fun key => next_residual runtime nonunit (clockRead 0) samples key budgets,
        merged_next_source runtime nonunit (clockRead 0) SourceConditionalNativeMerge.forgetClock samples budgets,
        fun key supported actor => full_mixture runtime nonunit samples key supported actor budgets,
        fun depth => ⟨field_decoder_source runtime nonunit samples depth budgets,
          table_next runtime nonunit samples depth budgets, compression_loss runtime nonunit samples depth budgets,
          fun enough => compression_positive runtime nonunit samples depth enough budgets⟩⟩⟩⟩

end
end SourceReceivedKeyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
