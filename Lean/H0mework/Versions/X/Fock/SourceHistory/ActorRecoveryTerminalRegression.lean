import H0mework.Versions.X.Fock.SourceHistory.ActorRecoveryMeanRegression

/-! The old actual next pays its own loss in addition to the actor-to-field loss. -/

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

theorem next_weight_one :
    observed (historyPMF 2) (nextAtom pulse runtimeSeed 2) (fieldPoint pulse 1) = 1 := by
  have constant : nextAtom pulse runtimeSeed 2 = Function.const (Fin 3) (fieldPoint pulse 1) := funext next_sample
  rw [observed, constant, PMF.map_const, PMF.pure_apply_self]

theorem next_mean_one :
    SourceGeneratedEmpiricalHilbert.transfer pulse runtimeSeed 2
        (actorTransfer pulse runtimeSeed 2 (taskValue (historyPMF 2) clockTask)) (fieldPoint pulse 1) = 1 := by
  rw [completeTransfer_is_conditional]
  have weighted := weighted_optimal (historyPMF 2) (nextAtom pulse runtimeSeed 2) clockTask (fieldPoint pulse 1)
  rw [next_weight_one] at weighted
  norm_num [Fin.sum_univ_succ, next_sample, clockTask_source, historyPMF_apply, Complex.real_smul] at weighted
  exact weighted

theorem optimal_cost_two_thirds :
    rawError pulse runtimeSeed 2 clockTask (fun atom => SourceGeneratedEmpiricalHilbert.transfer pulse runtimeSeed 2
      (actorTransfer pulse runtimeSeed 2 (taskValue (historyPMF 2) clockTask)) atom) = (2 / 3 : ℝ) := by
  norm_num [rawError, error, Fin.sum_univ_succ, next_sample, next_mean_one, clockTask_source, historyPMF_apply]

theorem field_loss_half :
    ‖SourceGeneratedEmpiricalHilbert.residual pulse runtimeSeed 2
      (actorTransfer pulse runtimeSeed 2 (taskValue (historyPMF 2) clockTask))‖ ^ 2 = (1 / 2 : ℝ) := by
  have attained := rawError_attains pulse runtimeSeed 2 clockTask
  dsimp only at attained
  have total := optimal_cost_two_thirds
  have early := actor_loss_sixth
  linarith only [attained, total, early]

theorem exact_clock_error (decoder : Field (process := process) pulse → ℂ) :
    rawError pulse runtimeSeed 2 clockTask decoder =
      (2 / 3 : ℝ) + ‖(1 : ℂ) - decoder (fieldPoint pulse 1)‖ ^ 2 := by
  have decomposition := actor_error_decomposition pulse runtimeSeed 2 clockTask decoder
  dsimp only at decomposition
  rw [actor_loss_sixth, field_loss_half] at decomposition
  apply decomposition.trans
  norm_num [SourceConditionalRecovery.decoderError, Fin.sum_univ_succ, next_sample, next_mean_one, historyPMF_apply]
  ring

theorem any_clock_decoder (decoder : Field (process := process) pulse → ℂ) :
    (2 / 3 : ℝ) ≤ rawError pulse runtimeSeed 2 clockTask decoder := by
  rw [exact_clock_error]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem constant_one_attains : rawError pulse runtimeSeed 2 clockTask (fun _ => 1) = (2 / 3 : ℝ) := by
  rw [exact_clock_error]
  norm_num

end
end SourceWeightedRecovery.Runtime.Actor.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
