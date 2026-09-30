import H0mework.Fock.HistoryConditional.ModelSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModel

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

def fullRead (runtime : LivingRuntimeState process) : Actors runtime → ℤ × ℤ :=
  SourceWeightedRecovery.Runtime.Actor.History.Clock.observe (inventoryBound runtime) 0

theorem full_supported (runtime : LivingRuntimeState process) (index : Actors runtime) :
    fullRead runtime index ∈ ((historyPMF (inventoryBound runtime)).map (fullRead runtime)).support :=
  SourceWeightedRecovery.Runtime.Actor.History.Clock.observation_supported (inventoryBound runtime) 0 index

theorem full_conditional_model (runtime : LivingRuntimeState process) (index : Actors runtime) :
    SourceConditionalNext.conditionalNext (historyPMF (inventoryBound runtime)) (fullRead runtime) (nextRead runtime)
      (fullRead runtime index) (full_supported runtime index) = PMF.pure (nextRead runtime index) :=
  SourceWeightedRecovery.Runtime.Actor.History.Clock.posterior_readback (inventoryBound runtime) 0 index (nextRead runtime)

def modelEstimate (runtime : LivingRuntimeState process) (value : ℤ × ℤ)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fullRead runtime)).support) : NextModel runtime :=
  ∑ index : Actors runtime,
    ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (fullRead runtime) value supported index).toReal : ℂ) •
      nextRead runtime index

theorem model_recovers (runtime : LivingRuntimeState process) (index : Actors runtime) :
    modelEstimate runtime (fullRead runtime index) (full_supported runtime index) = nextRead runtime index := by
  change (∑ candidate : Actors runtime,
    ((SourceWeightedRecovery.Runtime.Actor.History.Clock.posterior (inventoryBound runtime) 0 index candidate).toReal : ℂ) •
      nextRead runtime candidate) = _
  rw [SourceWeightedRecovery.Runtime.Actor.History.Clock.posterior_is_original, Finset.sum_eq_single index]
  · simp
  · intro candidate _ different
    rw [PMF.pure_apply, if_neg different]
    simp
  · intro missing
    exact (missing (Finset.mem_univ index)).elim

theorem original_task_recovers (runtime : LivingRuntimeState process) (decode : NextModel runtime → ℂ)
    (index : Actors runtime) :
    optimalDecoder (historyPMF (inventoryBound runtime)) (fullRead runtime) (decode ∘ nextRead runtime) (fullRead runtime index) =
      decode (nextRead runtime index) :=
  SourceWeightedRecovery.Runtime.Actor.History.Clock.optimum_recovers (inventoryBound runtime) 0 (decode ∘ nextRead runtime) index

theorem original_task_cost_zero (runtime : LivingRuntimeState process) (decode : NextModel runtime → ℂ) :
    error (historyPMF (inventoryBound runtime)) (fullRead runtime) (decode ∘ nextRead runtime)
      (optimalDecoder (historyPMF (inventoryBound runtime)) (fullRead runtime) (decode ∘ nextRead runtime)) = 0 :=
  SourceWeightedRecovery.Runtime.Actor.History.Clock.optimum_cost_zero (inventoryBound runtime) 0 (decode ∘ nextRead runtime)

theorem original_residual_zero (runtime : LivingRuntimeState process) (decode : NextModel runtime → ℂ) :
    residual (historyPMF (inventoryBound runtime)) (fullRead runtime) (taskValue (historyPMF (inventoryBound runtime)) (decode ∘ nextRead runtime)) = 0 :=
  SourceWeightedRecovery.Runtime.Actor.History.Clock.source_residual_zero (inventoryBound runtime) 0 (decode ∘ nextRead runtime)

theorem full_information_zero (runtime : LivingRuntimeState process) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (fullRead runtime)
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) = 0 := by
  apply (SourceConditionalNext.Image.entropy_zero_iff _ _ _ (positive runtime)).mpr
  intro left right same
  exact congrArg (nextRead runtime) (SourceWeightedRecovery.Runtime.Actor.History.Clock.observe_injective (inventoryBound runtime) 0 same)

theorem full_same_material (runtime : LivingRuntimeState process) (index candidate : Actors runtime)
    (supported : candidate ∈ (SourceWeightedRecovery.Runtime.Actor.History.Clock.posterior (inventoryBound runtime) 0 index).support) :
    HEq ((history runtimeSeed (inventoryBound runtime)).stageAt candidate) ((history runtimeSeed (inventoryBound runtime)).stageAt index) :=
  SourceWeightedRecovery.Runtime.Actor.History.Clock.posterior_same_material (inventoryBound runtime) 0 index candidate supported

end
end SourceConditionalModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
