import H0mework.Fock.HistoryConditional.InventoryOriginal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% (SourceConditionalModel.original_runtime runtime) ∧ type_of% (next_runtime runtime) ∧ type_of% (born_current runtime) ∧
  (∀ index : SourceConditionalModel.Actors runtime,
    type_of% (values_retained (inventoryBound runtime) index) ∧ type_of% (material_retained (inventoryBound runtime) index) ∧
    type_of% (values_original runtime index)) ∧
  (∀ depth : Nat,
    (∀ value : Field parity, type_of% (new_support_iff (inventoryBound runtime) depth value)) ∧
    (∀ value : Field parity, ∀ supported : value ∈ ((historyPMF (inventoryBound runtime)).map (observation (inventoryBound runtime) depth)).support,
      type_of% (conditional_mean_append (inventoryBound runtime) depth value supported) ∧
      type_of% (conditional_variance_append (inventoryBound runtime) depth value supported) ∧
      type_of% (mean_original runtime depth value supported) ∧
      ∀ guess : SourceJointClockGraph.Carrier, type_of% (conditional_error_append (inventoryBound runtime) depth value supported guess)) ∧
    (∀ fresh : bornObservation (inventoryBound runtime) depth ∉ ((historyPMF (inventoryBound runtime)).map (observation (inventoryBound runtime) depth)).support,
      type_of% (fresh_posterior (inventoryBound runtime) depth fresh) ∧
      type_of% (fresh_recovers (inventoryBound runtime) depth fresh) ∧
      type_of% (fresh_variance_zero (inventoryBound runtime) depth fresh)) ∧
    (∀ decoder : Field parity → SourceJointClockGraph.Carrier,
      type_of% (recovery_error_original runtime depth decoder) ∧ type_of% (current_error_append runtime depth decoder)) ∧
    type_of% (current_total_minimum runtime depth)) ∧
  type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨SourceConditionalModel.original_runtime runtime, next_runtime runtime, born_current runtime,
    (fun index => ⟨values_retained (inventoryBound runtime) index, material_retained (inventoryBound runtime) index, values_original runtime index⟩),
    (fun depth => ⟨new_support_iff (inventoryBound runtime) depth,
      (fun value supported => ⟨conditional_mean_append (inventoryBound runtime) depth value supported,
        conditional_variance_append (inventoryBound runtime) depth value supported, mean_original runtime depth value supported,
        conditional_error_append (inventoryBound runtime) depth value supported⟩),
      (fun fresh => ⟨fresh_posterior (inventoryBound runtime) depth fresh, fresh_recovers (inventoryBound runtime) depth fresh,
        fresh_variance_zero (inventoryBound runtime) depth fresh⟩),
      (fun decoder => ⟨recovery_error_original runtime depth decoder, current_error_append runtime depth decoder⟩),
      current_total_minimum runtime depth⟩), material.factorizes⟩

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
