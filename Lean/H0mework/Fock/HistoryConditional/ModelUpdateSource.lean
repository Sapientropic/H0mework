import H0mework.Fock.HistoryConditional.InnovationMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModelUpdate

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u

theorem retained_source (runtime : LivingRuntimeState process) (index : Actors runtime) :
    SourceConditionalVector.realizeModel runtime.tick.next (SourceActualImageStep.retainModel runtime (nextRead runtime index)) =
      SourceConditionalVector.realizeModel runtime (nextRead runtime index) := by
  have paid := SourceActualImageStep.retain_read runtime (SourceConditionalNext.Image.actual (nextRead runtime) index)
  dsimp only [SourceActualImageStep.read, SourceActualImageStep.retain, SourceConditionalNext.Image.actual, Set.rangeFactorization] at paid
  exact paid

theorem retained_estimate (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) :
    SourceConditionalVector.realizeModel runtime.tick.next
      (SourceActualImageStep.retainModel runtime (SourceConditionalVector.estimate runtime query value supported)) =
        SourceConditionalVector.realizeModel runtime (SourceConditionalVector.estimate runtime query value supported) := by
  simp only [SourceConditionalVector.estimate, SourceActualImageStep.retainModel, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun vector =>
    ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported index).toReal : ℂ) • vector)
      (retained_source runtime index)

def modelDecoder (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed) : NextModel runtime :=
  if supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support then
    SourceConditionalVector.estimate runtime query value supported else 0

theorem model_decoder_realization (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed) :
    SourceConditionalVector.realizeModel runtime (modelDecoder runtime query value) =
      SourceConditionalVector.vectorDecoder runtime query value := by
  by_cases supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support
  · simp only [modelDecoder, SourceConditionalVector.vectorDecoder, dif_pos supported]
  · simp only [modelDecoder, SourceConditionalVector.vectorDecoder, dif_neg supported, map_zero]

theorem retained_decoder (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed) :
    SourceConditionalVector.realizeModel runtime.tick.next (SourceActualImageStep.retainModel runtime (modelDecoder runtime query value)) =
      SourceConditionalVector.vectorDecoder runtime query value := by
  by_cases supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support
  · simp only [modelDecoder, SourceConditionalVector.vectorDecoder, dif_pos supported, retained_estimate]
  · simp only [modelDecoder, SourceConditionalVector.vectorDecoder, dif_neg supported, SourceActualImageStep.retainModel, map_zero]

end
end SourceConditionalModelUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
