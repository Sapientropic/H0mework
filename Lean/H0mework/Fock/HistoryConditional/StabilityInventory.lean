import H0mework.Fock.HistoryConditional.StabilitySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorStability

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors NextModel)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u

theorem coordinate_inventory (bound : Nat) (value : SourceJointClockGraph.Carrier) :
    (∑ actor : Fin (bound + 1), ‖SourceGInformationCost.coordinateRead (actor.val + 1) value‖ ^ 2) ≤ ‖value‖ ^ 2 := by
  have finite := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ENNReal).toReal) value.fst.fst
    (Finset.univ.image (fun actor : Fin (bound + 1) => actor.val + 1))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at finite
  rw [Finset.sum_image] at finite
  · have contraction := (WithLp.norm_fst_le _ value.fst).trans (WithLp.norm_fst_le _ value)
    change (∑ actor : Fin (bound + 1), ‖value.fst.fst (actor.val + 1)‖ ^ 2) ≤ ‖value‖ ^ 2
    exact finite.trans (by nlinarith [norm_nonneg value.fst.fst, norm_nonneg value])
  · intro left _ right _ same
    exact Fin.ext (Nat.add_right_cancel same)

theorem clipped_inventory (bound : Nat) (left right : SourceJointClockGraph.Carrier) :
    (∑ actor : Fin (bound + 1),
      |(ENNReal.ofReal (SourceGInformationCost.coordinateRead (actor.val + 1) left).re).toReal -
        (ENNReal.ofReal (SourceGInformationCost.coordinateRead (actor.val + 1) right).re).toReal| ^ 2) ≤ ‖left - right‖ ^ 2 := by
  calc
    _ ≤ ∑ actor : Fin (bound + 1), ‖SourceGInformationCost.coordinateRead (actor.val + 1) (left - right)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro actor _
      rw [map_sub]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (clipped_difference _ _)
    _ ≤ _ := coordinate_inventory bound (left - right)

theorem weights_inventory (runtime : LivingRuntimeState process) (left right : NextModel runtime) :
    (∑ actor : Actors runtime,
      |(SourcePosteriorReadback.readWeight runtime left actor).toReal - (SourcePosteriorReadback.readWeight runtime right actor).toReal| ^ 2) ≤
      ‖SourceConditionalVector.realizeModel runtime left - SourceConditionalVector.realizeModel runtime right‖ ^ 2 := by
  exact clipped_inventory (inventoryBound runtime) (SourceConditionalVector.realizeModel runtime left) (SourceConditionalVector.realizeModel runtime right)

theorem posterior_inventory_error (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) (model : NextModel runtime) :
    (∑ actor : Actors runtime,
      |(SourcePosteriorReadback.readWeight runtime model actor).toReal -
        (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor).toReal| ^ 2) ≤
      ‖SourceConditionalVector.realizeModel runtime model -
        SourceConditionalVector.realizeModel runtime (SourceConditionalVector.estimate runtime query value supported)‖ ^ 2 := by
  simp only [← SourcePosteriorReadback.weight_estimate runtime query value supported]
  exact weights_inventory runtime model _

end
end SourcePosteriorStability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
