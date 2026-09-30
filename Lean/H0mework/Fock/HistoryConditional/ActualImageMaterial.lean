import H0mework.Fock.HistoryConditional.ActualImageDistribution

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors nextRead positive dynamicRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% (image_card runtime) ∧ type_of% (image_information_zero runtime) ∧
  type_of% (birth_read runtime) ∧ type_of% (first_read runtime) ∧ type_of% (recover_first runtime) ∧
  (∀ index : Actors runtime, type_of% (step_actual runtime index) ∧ type_of% (retain_actual runtime index) ∧
    type_of% (retained_material runtime index) ∧ type_of% (act_actual runtime index) ∧ type_of% (recover_actual runtime index) ∧
    type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index)) ∧
  (∀ value : Image runtime, type_of% (step_read runtime value) ∧ type_of% (retain_read runtime value) ∧ type_of% (act_recover runtime value)) ∧
  (∀ value : SourceImage runtime, type_of% (act_read runtime value) ∧ type_of% (recover_act runtime value)) ∧
  (∀ target : Image runtime.tick.next, type_of% (step_fibre runtime target) ∧ type_of% (retain_fibre runtime target) ∧
    type_of% (next_distribution_step runtime target) ∧ type_of% (next_distribution_retain runtime target)) ∧
  (∀ depth : Nat, type_of% (information_zero_iff_recovers runtime (dynamicRead runtime depth)) ∧
    ∀ value : Field parity, ∀ supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support,
      type_of% (conditional_step runtime (dynamicRead runtime depth) value supported) ∧
      type_of% (conditional_retain runtime (dynamicRead runtime depth) value supported)) ∧
  (∀ (Code : Type) [Fintype Code], type_of% (faithful_code_lower runtime (Code := Code))) ∧
  type_of% (source_effect_pmf runtime (historyPMF (inventoryBound runtime))) ∧
  type_of% (effect_source_pmf runtime (historyPMF (inventoryBound runtime))) ∧ type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨image_card runtime, image_information_zero runtime, birth_read runtime, first_read runtime, recover_first runtime,
    (fun index => ⟨step_actual runtime index, retain_actual runtime index, retained_material runtime index,
      act_actual runtime index, recover_actual runtime index, sample_factorizes runtimeSeed (inventoryBound runtime) index⟩),
    (fun value => ⟨step_read runtime value, retain_read runtime value, act_recover runtime value⟩),
    (fun value => ⟨act_read runtime value, recover_act runtime value⟩),
    (fun target => ⟨step_fibre runtime target, retain_fibre runtime target, next_distribution_step runtime target, next_distribution_retain runtime target⟩),
    (fun depth => ⟨information_zero_iff_recovers runtime (dynamicRead runtime depth), fun value supported =>
      ⟨conditional_step runtime (dynamicRead runtime depth) value supported, conditional_retain runtime (dynamicRead runtime depth) value supported⟩⟩),
    (fun Code _ => faithful_code_lower runtime (Code := Code)), source_effect_pmf runtime (historyPMF (inventoryBound runtime)),
    effect_source_pmf runtime (historyPMF (inventoryBound runtime)), material.factorizes⟩

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
