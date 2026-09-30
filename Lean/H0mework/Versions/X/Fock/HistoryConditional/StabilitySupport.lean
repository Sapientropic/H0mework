import H0mework.Versions.X.Fock.HistoryConditional.StabilityInventory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorStability

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors NextModel)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
universe u

theorem weight_gap (runtime : LivingRuntimeState process) {Observed : Type u}
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support)
    (actor : Actors runtime) (seen : query actor = value) :
    1 / (inventoryBound runtime + 1 : ℝ) ≤
      (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor).toReal := by
  have weighted := SourceConditionalHistory.weighted_conditional (historyPMF (inventoryBound runtime)) query value supported actor
  rw [if_pos seen] at weighted
  have paid := congrArg ENNReal.toReal weighted
  simp only [ENNReal.toReal_mul, SourceUniformFibreVariance.source_weight] at paid
  have upper : (((historyPMF (inventoryBound runtime)).map query) value).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (((historyPMF (inventoryBound runtime)).map query).coe_le_one value)
  have nonnegative := ENNReal.toReal_nonneg (a := SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor)
  nlinarith

def threshold (runtime : LivingRuntimeState process) : ℝ := 1 / (2 * (inventoryBound runtime + 1 : ℝ))

theorem threshold_positive (runtime : LivingRuntimeState process) : 0 < threshold runtime := by
  unfold threshold
  positivity

theorem threshold_double (runtime : LivingRuntimeState process) :
    2 * threshold runtime = 1 / (inventoryBound runtime + 1 : ℝ) := by
  unfold threshold
  have nonzero : (inventoryBound runtime + 1 : ℝ) ≠ 0 := by positivity
  field_simp

def restoredSupport (runtime : LivingRuntimeState process) (model : NextModel runtime) : Finset (Actors runtime) :=
  Finset.univ.filter (fun actor => threshold runtime < (SourcePosteriorReadback.readWeight runtime model actor).toReal)

theorem support_restored (runtime : LivingRuntimeState process) {Observed : Type u} [DecidableEq Observed]
    (query : Actors runtime → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map query).support) (model : NextModel runtime)
    (small : ‖SourceConditionalVector.realizeModel runtime model -
      SourceConditionalVector.realizeModel runtime (SourceConditionalVector.estimate runtime query value supported)‖ < threshold runtime) :
    restoredSupport runtime model = SourceUniformFibreVariance.fibre (inventoryBound runtime) query value := by
  ext actor
  simp only [restoredSupport, Finset.mem_filter, Finset.mem_univ, true_and, SourceUniformFibreVariance.fibre_mem]
  have error := lt_of_le_of_lt (posterior_weight_error runtime query value supported model actor) small
  have bounds := abs_lt.mp error
  constructor
  · intro above
    by_contra missing
    have zero : SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) query value supported actor = 0 := by
      rw [SourceConditionalHistory.conditional_apply, if_neg missing]
    rw [zero, ENNReal.toReal_zero, sub_zero] at bounds
    linarith
  · intro seen
    have gap := weight_gap runtime query value supported actor seen
    rw [← threshold_double] at gap
    linarith

end
end SourcePosteriorStability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
