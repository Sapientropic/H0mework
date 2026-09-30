import H0mework.Fock.SourceHistory.CountedMerge.Consumer
import H0mework.Fock.SourceHistory.CountedAdvance.Consumer
import H0mework.Fock.SourceHistory.CountedAdvance.ModelContinuation
import H0mework.Fock.SourceHistory.CountedPosterior.Consumer
import H0mework.Fock.SourceHistory.CountedPosterior.Continuation
import H0mework.Fock.SourceHistory.CountedPosterior.Field
import H0mework.Fock.SourceHistory.CountedRecovery.Field
import H0mework.Fock.SourceHistory.CountedObservation.Complete

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ (nonunit : (maximumIndex runtime).val ≠ 0) (keys : List (ℤ × ℤ))
      (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
      (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
      (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
        SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
          (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
            SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
              (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) (steps : Nat),
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
    let current := SourceRetainedReceiver.trajectory runtime initial (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
    let table := run (inventoryBound runtime) (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) (fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    type_of% (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) ∧
    type_of% (SourceCountedAdvance.continued_next runtime nonunit (clockRead 0) keys inventory samples budgets steps) ∧
    (∀ key : ℤ × ℤ, type_of% (readValue_source (runtime.advance steps) table current (clockRead 0) (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) key) ∧
      type_of% (read_residual (runtime.advance steps) table current (clockRead 0) (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) key) ∧ type_of% (SourceCountedPosterior.continued_source runtime nonunit (clockRead 0) keys inventory samples budgets steps key) ∧ type_of% (SourceCountedPosterior.continued_model runtime nonunit (clockRead 0) keys inventory samples budgets steps key) ∧ type_of% (SourceCountedAdvance.continued_model runtime nonunit (clockRead 0) keys inventory samples budgets steps key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound (runtime.advance steps))).map (fun actor : Actors (runtime.advance steps) => clockRead 0 actor.val)).support, type_of% (conditional_error (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table current (clockRead 0) key (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) supported)) ∧
    (∀ key : ZMod 2, type_of% (SourceCountedMerge.continued_source runtime nonunit (clockRead 0) keys inventory samples budgets SourceConditionalNativeMerge.forgetClock steps key) ∧ type_of% (SourceCountedMerge.continued_next_model runtime nonunit (clockRead 0) keys inventory samples budgets SourceConditionalNativeMerge.forgetClock steps key)) ∧
    (∀ depth : Nat, type_of% (field_balance (runtime.advance steps) table current (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) depth) ∧ type_of% (field_information (runtime.advance steps) table depth) ∧ type_of% (SourceCountedRecovery.field_update (runtime.advance steps) table current (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) depth) ∧ type_of% (SourceCountedPosterior.continued_field_balance runtime nonunit keys inventory samples budgets steps depth) ∧ type_of% (SourceCountedPosterior.continued_field_update runtime nonunit keys inventory samples budgets steps depth) ∧ type_of% (SourceCountedAdvance.continued_next_field runtime nonunit keys inventory samples budgets steps depth) ∧ type_of% (SourceCountedMerge.continued_next_field runtime nonunit keys inventory samples budgets steps depth))

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  refine ⟨material.factorizes, ?_⟩
  intro nonunit keys inventory samples budgets steps
  let initial : SourceRetainedReceiver.At runtime (ℤ × ℤ) := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
  let current := SourceRetainedReceiver.trajectory runtime initial (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
  let table := run (inventoryBound runtime) (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) (fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  with_reducible exact ⟨received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps,
    SourceCountedAdvance.continued_next runtime nonunit (clockRead 0) keys inventory samples budgets steps,
    fun key => ⟨readValue_source (runtime.advance steps) table current (clockRead 0) (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) key,
      read_residual (runtime.advance steps) table current (clockRead 0) (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) key, SourceCountedPosterior.continued_source runtime nonunit (clockRead 0) keys inventory samples budgets steps key, SourceCountedPosterior.continued_model runtime nonunit (clockRead 0) keys inventory samples budgets steps key, SourceCountedAdvance.continued_model runtime nonunit (clockRead 0) keys inventory samples budgets steps key, fun supported => conditional_error (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table current (clockRead 0) key (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) supported⟩,
    fun key => ⟨SourceCountedMerge.continued_source runtime nonunit (clockRead 0) keys inventory samples budgets SourceConditionalNativeMerge.forgetClock steps key, SourceCountedMerge.continued_next_model runtime nonunit (clockRead 0) keys inventory samples budgets SourceConditionalNativeMerge.forgetClock steps key⟩,
    fun depth => ⟨field_balance (runtime.advance steps) table current (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) depth, field_information (runtime.advance steps) table depth, SourceCountedRecovery.field_update (runtime.advance steps) table current (received_simulates runtime nonunit (clockRead 0) keys inventory samples budgets steps) (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) depth, SourceCountedPosterior.continued_field_balance runtime nonunit keys inventory samples budgets steps depth, SourceCountedPosterior.continued_field_update runtime nonunit keys inventory samples budgets steps depth, SourceCountedAdvance.continued_next_field runtime nonunit keys inventory samples budgets steps depth, SourceCountedMerge.continued_next_field runtime nonunit keys inventory samples budgets steps depth⟩⟩

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
