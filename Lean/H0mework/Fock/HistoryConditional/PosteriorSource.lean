import H0mework.Fock.HistoryConditional.ModelUpdateMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorReadback

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors NextModel)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u

theorem mean_coordinate (bound : Nat) (source : PMF (Fin (bound + 1))) (actor : Fin (bound + 1)) :
    SourceGInformationCost.coordinateRead (actor.val + 1) (SourceVectorMoment.mean source (SourceConditionalInventory.values bound)) =
      ((source actor).toReal : ℂ) := by
  rw [SourceVectorMoment.mean, map_sum]
  simp only [map_smul, SourceGInformationCost.coordinate_actual]
  rw [Finset.sum_eq_single actor]
  · simp only [ite_true, smul_eq_mul, mul_one]
  · intro other _ different
    rw [if_neg different, smul_zero]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem model_coordinate (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) (actor : Actors runtime) :
    SourceGInformationCost.coordinateRead (actor.val + 1)
      (SourceConditionalVector.realizeModel runtime (SourceConditionalVector.estimate runtime query value supported)) =
      ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor).toReal : ℂ) := by
  simp only [SourceConditionalVector.estimate_realization, ← SourceConditionalInventory.values_original runtime]
  exact mean_coordinate (inventoryBound runtime) _ actor

def readWeight (runtime : LivingRuntimeState process) (model : NextModel runtime) (actor : Actors runtime) : ENNReal :=
  ENNReal.ofReal (SourceGInformationCost.coordinateRead (actor.val + 1) (SourceConditionalVector.realizeModel runtime model)).re

theorem weight_estimate (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) (actor : Actors runtime) :
    readWeight runtime (SourceConditionalVector.estimate runtime query value supported) actor =
      SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor := by
  rw [readWeight, model_coordinate, Complex.ofReal_re]
  exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

theorem posterior_recovered (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) :
    readWeight runtime (SourceConditionalVector.estimate runtime query value supported) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor) :=
  funext (weight_estimate runtime query value supported)

end
end SourcePosteriorReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
