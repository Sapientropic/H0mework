import H0mework.Fock.PrimeFieldCalculation.InventoryTrace
import H0mework.Fock.PrimeFieldCalculation.InventoryRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedConditionalInventory

open SourceConditionalInventory SourceUniformFibreVariance SourceWeightedRecovery
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionMeasure
open SourceGeneratedAcquisitionJoint SourcePrimeHistoryRecovery
open SourceGeneratedActionWords.Fock.OriginalHilbert
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance : MeasurableSpace IntegralOneParticle := ⊤

theorem runtime_cost_step (runtime : LivingRuntimeState process) :
    snapshotCost (inventoryBound runtime.tick.next) = snapshotCost (inventoryBound runtime) +
      if Nat.Prime (2 * inventoryBound runtime + 5) then 0 else 1 := by
  have same := congrArg inventoryBound (advance_original runtime 1)
  change inventoryBound runtime.tick.next = inventoryBound (runtimeAt (runtime.state + 1)) at same
  rw [inventory_bound (runtimeAt (runtime.state + 1)), runtimeAt_state, ← inventory_bound runtime] at same
  exact (congrArg snapshotCost same).trans (actual_cost_step (inventoryBound runtime))

def InventoryAt (runtime : LivingRuntimeState process) (depth : Nat) : Prop :=
    let bound := inventoryBound runtime
    type_of% (source_step bound) ∧ type_of% (multiplicity_moves bound) ∧
    type_of% (runtime_cost_step runtime) ∧ type_of% (normal_cost runtime) ∧
    type_of% (generated_next_cost runtime) ∧ type_of% (snapshot_information bound) ∧
    (∀ decoder : Fin (bound + 1) → IntegralOneParticle → ℂ, type_of% (original_decoder_lower depth bound decoder)) ∧
    (∀ value : FieldSpace depth bound, type_of% (original_reconstruct depth bound value) ∧
      type_of% (original_energy depth bound value)) ∧
    type_of% (original_inventory_cost depth bound) ∧
    (∀ actor : Fin (bound + 1), type_of% (unit_is_original_cotest bound actor) ∧
      type_of% (original_unit_norm depth bound actor) ∧
      ∀ index : Fin (bound + 1), type_of% (full_record_read runtime depth
        (SourceWeightedRecovery.residual (historyPMF bound) (fun point => rawField point.val)
          (taskValue (historyPMF bound) (fun point => (unitTask bound actor point : ℂ)))) index)) ∧
    type_of% (full_record_cost_zero runtime depth) ∧
    type_of% (acquisition_consumed runtime) ∧ type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes runtime.tick.next .particleWave) ∧
    type_of% (SourceOperationNative.Observed.model_factorizes (process := process) rawField runtime)

theorem inventory_consumed (runtime : LivingRuntimeState process) (depth : Nat) : InventoryAt runtime depth := by
  dsimp only [InventoryAt]
  exact ⟨source_step _, multiplicity_moves _, runtime_cost_step runtime, normal_cost runtime, generated_next_cost runtime, snapshot_information _,
    original_decoder_lower depth _, (fun value => ⟨original_reconstruct depth _ value, original_energy depth _ value⟩),
    original_inventory_cost depth _, (fun actor => ⟨unit_is_original_cotest _ actor, original_unit_norm depth _ actor,
      full_record_read runtime depth _⟩), full_record_cost_zero runtime depth, acquisition_consumed runtime,
    coversAt_factorizes runtime .particleWave, coversAt_factorizes runtime.tick.next .particleWave,
    SourceOperationNative.Observed.model_factorizes (process := process) rawField runtime⟩

def RecoveryAt (round : Nat) : Prop :=
    InventoryAt (roundRuntime round) (depth (roundRuntime round)) ∧
      type_of% (SourceGeneratedBornDecoder.sourceGeneratedBornDecoderRecovery round)

theorem sourceGeneratedConditionalInventoryRecovery (round : Nat) : RecoveryAt round :=
  ⟨inventory_consumed (roundRuntime round) (depth (roundRuntime round)),
    SourceGeneratedBornDecoder.sourceGeneratedBornDecoderRecovery round⟩

end
end SourceGeneratedConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
