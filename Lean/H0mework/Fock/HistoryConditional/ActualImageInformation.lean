import H0mework.Fock.HistoryConditional.ActualImageSourceImage

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors nextRead positive)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

theorem information_zero_iff_injective (runtime : LivingRuntimeState process) {Observed : Type u}
    (observation : Actors runtime → Observed) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) observation
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) = 0 ↔ Function.Injective observation := by
  rw [SourceConditionalNext.Image.entropy_zero_iff]
  constructor
  · intro determined left right same
    exact nextRead_injective runtime (determined left right same)
  · intro injective left right same
    exact congrArg (nextRead runtime) (injective same)

theorem decoder_recovers_of_injective (runtime : LivingRuntimeState process) {Observed : Type u}
    (observation : Actors runtime → Observed) (injective : Function.Injective observation) (index : Actors runtime) :
    SourceConditionalVector.vectorDecoder runtime observation (observation index) =
      SourceConditionalInventory.values (inventoryBound runtime) index := by
  have supported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) observation index (positive runtime index)
  rw [SourceConditionalVector.vectorDecoder, dif_pos supported, SourceConditionalVector.estimate_realization,
    SourceWeightedRecovery.ObservationRefinement.conditional_injective (historyPMF (inventoryBound runtime)) observation injective index (positive runtime index),
    Finset.sum_eq_single index]
  · simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
    exact (SourceConditionalInventory.values_original runtime index).symm
  · intro other _ different
    rw [PMF.pure_apply, if_neg different]
    simp only [ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem information_zero_iff_recovers (runtime : LivingRuntimeState process) {Observed : Type u}
    (observation : Actors runtime → Observed) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) observation
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) = 0 ↔
    ∀ index, SourceConditionalVector.vectorDecoder runtime observation (observation index) =
      SourceConditionalInventory.values (inventoryBound runtime) index := by
  rw [information_zero_iff_injective]
  constructor
  · exact fun injective => decoder_recovers_of_injective runtime observation injective
  · intro recovers left right same
    apply values_injective runtime
    exact (recovers left).symm.trans
      ((congrArg (SourceConditionalVector.vectorDecoder runtime observation) same).trans (recovers right))

theorem image_information_zero (runtime : LivingRuntimeState process) :
    SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime))
      (SourceConditionalNext.Image.actual (nextRead runtime))
      (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime) = 0 := by
  apply (information_zero_iff_injective runtime _).mpr
  intro left right same
  exact nextRead_injective runtime (congrArg Subtype.val same)

theorem source_effect_pmf (runtime : LivingRuntimeState process) (source : PMF (Actors runtime)) :
    (source.map (SourceConditionalNext.Image.actual (SourceConditionalVector.actor runtime))).map (act runtime) =
      source.map (SourceConditionalNext.Image.actual (nextRead runtime)) := by
  rw [PMF.map_comp]
  apply congrArg (fun reader => source.map reader)
  funext index
  exact act_actual runtime index

theorem effect_source_pmf (runtime : LivingRuntimeState process) (source : PMF (Actors runtime)) :
    (source.map (SourceConditionalNext.Image.actual (nextRead runtime))).map (recover runtime) =
      source.map (SourceConditionalNext.Image.actual (SourceConditionalVector.actor runtime)) := by
  rw [PMF.map_comp]
  apply congrArg (fun reader => source.map reader)
  funext index
  exact recover_actual runtime index

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
