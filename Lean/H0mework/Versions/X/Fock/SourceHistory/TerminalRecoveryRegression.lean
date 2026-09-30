import H0mework.Probability.EmpiricalRecovery.HistoryConditional
import H0mework.Versions.X.Fock.SourceHistory.ConditionalRecoveryRegression

/-! The original pulse keeps its sharp recovery floor at every actual finite future depth. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery.History.Pulse

open SourceGeneratedEmpiricalHilbert SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer SourceConditionalTransfer.Pulse
open SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem any_future_decoder (depth : Nat) (decoder : Field (process := process) pulse → ℂ) :
    (1 / 4 : ℝ) ≤ terminalError pulse runtimeSeed 1 depth indicatorValue decoder :=
  SourceConditionalRecovery.Pulse.residual_energy.symm.trans_le
    (first_loss_persists pulse runtimeSeed 1 depth indicatorValue decoder)

theorem constant_half_attains (depth : Nat) :
    terminalError pulse runtimeSeed 1 depth indicatorValue (fun _ => (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  apply (Fin.sum_univ_two (fun index : Fin 2 => (historyPMF 1 index).toReal *
    ‖indicatorValue (fieldSample pulse runtime 1 index) - (1 / 2 : ℂ)‖ ^ 2)).trans
  rw [source_zero_value, source_one_value]
  norm_num [historyPMF_apply]

theorem complete_floor (depth : Nat) :
    inventoryEnergy pulse runtimeSeed 1 (depth + 1) (retainedHistory pulse runtimeSeed 1 (depth + 1) indicatorValue).2 =
      (1 / 4 : ℝ) := by
  have lower := any_future_decoder depth
    (fun atom => (retainedHistory pulse runtimeSeed 1 (depth + 1) indicatorValue).1 atom)
  have attained := terminalError_attains pulse runtimeSeed 1 depth indicatorValue
  exact le_antisymm
    ((terminalError_lower_bound pulse runtimeSeed 1 depth indicatorValue (fun _ => (1 / 2 : ℂ))).trans_eq
      (constant_half_attains depth)) (lower.trans_eq attained)

theorem no_future_exact_decoder (depth : Nat) (decoder : Field (process := process) pulse → ℂ) :
    ¬ ∀ index : Fin 2,
      decoder (fieldSample pulse (runtimeSeed.advance (depth + 1)) 1 index) =
        indicatorValue (fieldSample pulse runtimeSeed 1 index) := by
  intro exactDecoder
  have zeroError : terminalError pulse runtimeSeed 1 depth indicatorValue decoder = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    have difference : indicatorValue (fieldSample pulse runtimeSeed 1 index) -
        decoder (fieldSample pulse (runtimeSeed.advance (depth + 1)) 1 index) = 0 :=
      sub_eq_zero.mpr (exactDecoder index).symm
    exact (congrArg (fun error : ℂ => (historyPMF 1 index).toReal * ‖error‖ ^ 2) difference).trans (by simp)
  have lower := any_future_decoder depth decoder
  rw [zeroError] at lower
  norm_num at lower

end
end SourceConditionalRecovery.History.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
