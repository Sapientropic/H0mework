import H0mework.Fock.HistoryConditional.GCostOriginal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ actor : Actors runtime, type_of% (coordinate_cotest (inventoryBound runtime) actor) ∧
    type_of% (unit_original_coordinate (inventoryBound runtime) actor) ∧
    type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) actor)) ∧
  (∀ depth : Nat, type_of% (variance_original runtime depth) ∧ type_of% (current_full_variance runtime depth) ∧
    type_of% (current_information_lower runtime depth) ∧
    ∀ decoder : Field parity → SourceJointClockGraph.Carrier,
      type_of% (current_error_account runtime depth decoder) ∧ type_of% (current_decoder_lower runtime depth decoder)) ∧
  (∀ (Code : Type) [Fintype Code] [DecidableEq Code] [MeasurableSpace Code] [MeasurableSingletonClass Code],
    ∀ query : Actors runtime → Code,
      type_of% (full_variance_cost (inventoryBound runtime) query) ∧ type_of% (capacity_lower (inventoryBound runtime) query) ∧
      ∀ decoder : Code → SourceJointClockGraph.Carrier, type_of% (error_account (inventoryBound runtime) query decoder) ∧
        type_of% (decoder_capacity_lower (inventoryBound runtime) query decoder)) ∧
  type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun actor => ⟨coordinate_cotest (inventoryBound runtime) actor,
    unit_original_coordinate (inventoryBound runtime) actor, sample_factorizes runtimeSeed (inventoryBound runtime) actor⟩),
    (fun depth => ⟨variance_original runtime depth, current_full_variance runtime depth, current_information_lower runtime depth,
      fun decoder => ⟨current_error_account runtime depth decoder, current_decoder_lower runtime depth decoder⟩⟩),
    (fun Code _ _ _ _ query => ⟨full_variance_cost (inventoryBound runtime) query, capacity_lower (inventoryBound runtime) query,
      fun decoder => ⟨error_account (inventoryBound runtime) query decoder, decoder_capacity_lower (inventoryBound runtime) query decoder⟩⟩),
    material.factorizes⟩

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
