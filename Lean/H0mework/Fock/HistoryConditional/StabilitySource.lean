import H0mework.Fock.HistoryConditional.PosteriorMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorStability

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors NextModel)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
universe u

theorem coordinate_norm (address : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖SourceGInformationCost.coordinateRead address value‖ ≤ ‖value‖ := by
  change ‖value.fst.fst address‖ ≤ ‖value‖
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) value.fst.fst address).trans
    ((WithLp.norm_fst_le _ value.fst).trans (WithLp.norm_fst_le _ value))

theorem coordinate_difference (address : Nat) (left right : SourceJointClockGraph.Carrier) :
    ‖SourceGInformationCost.coordinateRead address left - SourceGInformationCost.coordinateRead address right‖ ≤ ‖left - right‖ := by
  rw [← map_sub]
  exact coordinate_norm address (left - right)

theorem clipped_difference (left right : ℂ) :
    |(ENNReal.ofReal left.re).toReal - (ENNReal.ofReal right.re).toReal| ≤ ‖left - right‖ := by
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  have clipped := abs_max_sub_max_le_max left.re 0 right.re 0
  simp only [sub_self, abs_zero] at clipped
  exact clipped.trans (max_le
    (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (left - right)) (norm_nonneg _))

theorem weights_difference (runtime : LivingRuntimeState process) (left right : NextModel runtime) (actor : Actors runtime) :
    |(SourcePosteriorReadback.readWeight runtime left actor).toReal - (SourcePosteriorReadback.readWeight runtime right actor).toReal| ≤
      ‖SourceConditionalVector.realizeModel runtime left - SourceConditionalVector.realizeModel runtime right‖ :=
  (clipped_difference _ _).trans (coordinate_difference _ _ _)

theorem posterior_weight_error (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) (model : NextModel runtime) (actor : Actors runtime) :
    |(SourcePosteriorReadback.readWeight runtime model actor).toReal -
      (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor).toReal| ≤
      ‖SourceConditionalVector.realizeModel runtime model -
        SourceConditionalVector.realizeModel runtime (SourceConditionalVector.estimate runtime query value supported)‖ := by
  rw [← SourcePosteriorReadback.weight_estimate runtime query value supported actor]
  exact weights_difference runtime model _ actor

end
end SourcePosteriorStability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
