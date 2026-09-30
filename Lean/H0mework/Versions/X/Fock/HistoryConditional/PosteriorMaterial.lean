import H0mework.Versions.X.Fock.HistoryConditional.PosteriorConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorReadback

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceConditionalModel (Actors dynamicRead positive)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (dynamic_information_recovered runtime depth) ∧ type_of% (updated_information_recovered runtime depth) ∧
    type_of% (recovered_information_cost runtime depth) ∧
    (∀ enough : 2 ≤ inventoryBound runtime.tick.next, type_of% (updated_mixture_not_actual runtime enough depth)) ∧
    ∀ value : Field parity, ∀ supported : value ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (dynamicRead runtime.tick.next depth)).support,
      type_of% (updated_posterior runtime depth value supported) ∧ ∀ actor : Actors runtime.tick.next,
        type_of% (updated_support runtime depth value supported actor) ∧ type_of% (updated_eq_source_iff runtime depth value supported actor)) ∧
  (∀ depth : Nat, ∀ index : Actors runtime,
    type_of% (posterior_recovered runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
      (SourceWeightedRecovery.observed_supported _ _ index (positive runtime index))) ∧
    type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index)) ∧
  type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨dynamic_information_recovered runtime depth, updated_information_recovered runtime depth,
    recovered_information_cost runtime depth, (fun enough => updated_mixture_not_actual runtime enough depth),
    fun value supported => ⟨updated_posterior runtime depth value supported,
      fun actor => ⟨updated_support runtime depth value supported actor, updated_eq_source_iff runtime depth value supported actor⟩⟩⟩),
    (fun depth index => ⟨posterior_recovered runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
      (SourceWeightedRecovery.observed_supported _ _ index (positive runtime index)), sample_factorizes runtimeSeed (inventoryBound runtime) index⟩),
    material.factorizes⟩

end
end SourcePosteriorReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
