import H0mework.Versions.X.Fock.PrimeFieldCalculation.FixedField
import H0mework.Versions.X.Fock.PrimeFieldCalculation.FixedProbability
import H0mework.Versions.X.Fock.PrimeFieldCalculation.FixedEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFixedInventoryRecovery

open SourceGeneratedActionObservationHistory SourceConditionalHistory
open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint
open SourceGeneratedRuntimeHistoryProbability SourcePrimeHistoryRecovery SourceConditionalInventory SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance consumerObservationMeasurable (width : Nat) : MeasurableSpace (Observation width) := ⊤

def StageAt (runtime : LivingRuntimeState process) (depth width : Nat)
    (inside : width ≤ windowBound sourceOwner (inventoryBound runtime)) : Prop :=
    (∀ actor : Fin (inventoryBound runtime + 1), ∀ time : Fin (width + 1),
      type_of% (query_actual_material runtime width inside actor time)) ∧
    (∀ actor : Fin (inventoryBound runtime + 1), type_of% (originalRead_next runtime depth width inside actor)) ∧
    (∀ decoder : Fin (inventoryBound runtime + 1) → Observation width → ℂ,
      type_of% (original_decoder_lower runtime depth width inside decoder)) ∧
    (∀ value : FieldSpace depth (inventoryBound runtime),
      type_of% (original_reconstruct runtime depth width value) ∧ type_of% (original_energy runtime depth width value)) ∧
    type_of% (original_inventory_cost runtime depth width) ∧
    (∀ actor index : Fin (inventoryBound runtime + 1),
      type_of% (SourceGeneratedConditionalInventory.full_record_read runtime depth
        (SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) (query runtime width)
          (taskValue (historyPMF (inventoryBound runtime)) (fun point => (unitTask (inventoryBound runtime) actor point : ℂ)))) index))

theorem stage_consumed (runtime : LivingRuntimeState process) (depth width : Nat)
    (inside : width ≤ windowBound sourceOwner (inventoryBound runtime)) : StageAt runtime depth width inside := by
  dsimp only [StageAt]
  exact ⟨query_actual_material runtime width inside, originalRead_next runtime depth width inside,
    original_decoder_lower runtime depth width inside,
    (fun value => ⟨original_reconstruct runtime depth width value, original_energy runtime depth width value⟩),
    original_inventory_cost runtime depth width,
    (fun _actor => SourceGeneratedConditionalInventory.full_record_read runtime depth _)⟩

def RecoveryAt (runtime : LivingRuntimeState process) : Prop :=
    (∀ width : Fin (windowBound sourceOwner (inventoryBound runtime) + 1),
      StageAt runtime (depth runtime) width.val (by omega)) ∧
    (∀ width : Fin (windowBound sourceOwner (inventoryBound runtime)),
      type_of% (cost_refinement runtime width.val) ∧ type_of% (recovered_distinctions runtime width.val) ∧
      (∀ value : Observation width.val, ∀ supported : value ∈
        (SourceConditionalHistory.observed (SourceConditionalHistory.observed (historyPMF (inventoryBound runtime)) (query runtime (width.val + 1)))
          (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width.val)).support,
        type_of% (complete_conditional runtime width.val value supported)) ∧
      ∀ actor : Fin (inventoryBound runtime + 1), type_of% (query_tail_birth runtime width.val actor)) ∧
    type_of% (cost_antitone runtime) ∧ type_of% (complete_record runtime) ∧ type_of% (complete_cost_zero runtime) ∧
    type_of% (SourceGeneratedConditionalInventory.inventory_consumed runtime (depth runtime)) ∧
    type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave)

theorem sourceGeneratedFixedInventoryRecovery (runtime : LivingRuntimeState process) : RecoveryAt runtime := by
  dsimp only [RecoveryAt]
  exact ⟨(fun width => stage_consumed runtime (depth runtime) width.val (by omega)),
    (fun width => ⟨cost_refinement runtime width.val, recovered_distinctions runtime width.val,
      complete_conditional runtime width.val, query_tail_birth runtime width.val⟩), cost_antitone runtime, complete_record runtime, complete_cost_zero runtime,
    SourceGeneratedConditionalInventory.inventory_consumed runtime (depth runtime),
    coversAt_factorizes runtime .particleWave,
    coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave⟩

theorem actual_recovery_consumed :
    RecoveryAt (runtimeAt 2) ∧ type_of% actual_prefix_recovery ∧
      type_of% (coversAt_factorizes (runtimeAt 2).tick.next .particleWave) ∧
      type_of% (coversAt_factorizes (runtimeAt 2).tick.next.tick.next .particleWave) :=
  ⟨sourceGeneratedFixedInventoryRecovery (runtimeAt 2), actual_prefix_recovery,
    coversAt_factorizes (runtimeAt 2).tick.next .particleWave,
    coversAt_factorizes (runtimeAt 2).tick.next.tick.next .particleWave⟩

end
end SourceFixedInventoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
