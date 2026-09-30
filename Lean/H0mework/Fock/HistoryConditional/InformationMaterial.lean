import H0mework.Fock.HistoryConditional.InformationRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInformationReadback

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (dynamic_information runtime depth) ∧ type_of% (dynamic_information_code runtime depth) ∧
    type_of% (dynamic_information_lower runtime depth) ∧ type_of% (model_information_cost runtime depth) ∧
    type_of% (dynamic_variance_capacity runtime depth) ∧
    ∀ decoder : Field parity → SourceJointClockGraph.Carrier,
      type_of% (model_decoder_cost runtime depth decoder) ∧ type_of% (dynamic_decoder_capacity runtime depth decoder) ∧
      type_of% (dynamic_budget_inventory runtime depth decoder)) ∧
  (∀ depth : Nat, ∀ index : Actors runtime, type_of% (dynamic_conditional runtime depth index) ∧
    type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index)) ∧
  type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨dynamic_information runtime depth, dynamic_information_code runtime depth,
    dynamic_information_lower runtime depth, model_information_cost runtime depth, dynamic_variance_capacity runtime depth,
    fun decoder => ⟨model_decoder_cost runtime depth decoder, dynamic_decoder_capacity runtime depth decoder,
      dynamic_budget_inventory runtime depth decoder⟩⟩),
    (fun depth index => ⟨dynamic_conditional runtime depth index, sample_factorizes runtimeSeed (inventoryBound runtime) index⟩),
    material.factorizes⟩

end
end SourceInformationReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
