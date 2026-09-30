import H0mework.Fock.SourceHistory.ActorRecoverySourceRegression

/-! The complete original three-actor distribution computes the first, previously projected-away loss. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.Pulse

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedEmpiricalHilbert.Controls SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical

noncomputable section

local instance : UniformSpace (Field pulse) := fieldUniform pulse
local instance : MeasurableSpace (Field pulse) := fieldBorel pulse
local instance : BorelSpace (Field pulse) := ⟨rfl⟩
local instance : T2Space (Field pulse) := field_t2 pulse

theorem current_weight_zero :
    observed (historyPMF 2) (fieldSample pulse runtimeSeed 2) (fieldPoint pulse 0) = (1 / 3 : ENNReal) := by
  norm_num [observed, PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, current_fibre,
    historyPMF_apply, point_zero_ne_one]

theorem current_weight_one :
    observed (historyPMF 2) (fieldSample pulse runtimeSeed 2) (fieldPoint pulse 1) = (2 / 3 : ENNReal) := by
  norm_num [observed, PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, current_fibre,
    historyPMF_apply, point_zero_ne_one.symm, div_eq_mul_inv]

theorem current_mean_zero :
    actorTransfer pulse runtimeSeed 2 (taskValue (historyPMF 2) clockTask) (fieldPoint pulse 0) = 0 := by
  rw [actorTransfer_is_conditional]
  have weighted := weighted_optimal (historyPMF 2) (fieldSample pulse runtimeSeed 2) clockTask (fieldPoint pulse 0)
  rw [current_weight_zero] at weighted
  norm_num [Fin.sum_univ_succ, current_fibre, clockTask_source, historyPMF_apply,
    point_zero_ne_one.symm, Complex.real_smul] at weighted
  exact weighted

theorem current_mean_one :
    actorTransfer pulse runtimeSeed 2 (taskValue (historyPMF 2) clockTask) (fieldPoint pulse 1) = (3 / 2 : ℂ) := by
  rw [actorTransfer_is_conditional]
  have weighted := weighted_optimal (historyPMF 2) (fieldSample pulse runtimeSeed 2) clockTask (fieldPoint pulse 1)
  rw [current_weight_one] at weighted
  norm_num [Fin.sum_univ_succ, current_fibre, clockTask_source, historyPMF_apply,
    point_zero_ne_one, Complex.real_smul] at weighted
  linear_combination (3 / 2 : ℂ) * weighted

theorem current_mean_sample (index : Fin 3) :
    actorTransfer pulse runtimeSeed 2 (taskValue (historyPMF 2) clockTask) (fieldSample pulse runtimeSeed 2 index) =
      if index = 0 then 0 else (3 / 2 : ℂ) := by
  rw [current_fibre]
  split_ifs <;> first | exact current_mean_zero | exact current_mean_one

theorem actor_loss_sixth :
    ‖actorResidual pulse runtimeSeed 2 (taskValue (historyPMF 2) clockTask)‖ ^ 2 = (1 / 6 : ℝ) := by
  rw [source_actor_minimum]
  norm_num [error, Fin.sum_univ_succ, current_mean_sample, clockTask_source, historyPMF_apply]

end
end SourceWeightedRecovery.Runtime.Actor.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
