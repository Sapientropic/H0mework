import H0mework.Versions.X.Fock.SourceHistoryClock.RecoveryDecoder
import H0mework.Versions.X.Fock.SourceHistory.ActorRecoveryTerminalRegression

/-! The same actual actor task has a sharp restricted-observation cost and a source-owned exact recovery. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Controls

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedEmpiricalHilbert.Controls SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem clock_task_is_original : Clock.task 2 = Pulse.clockTask := rfl

theorem pulse_cost_lower (depth : Nat) (decoder : Field (process := process) pulse → ℂ) :
    (2 / 3 : ℝ) ≤ rawTerminalError pulse runtimeSeed 2 depth (Clock.task 2) decoder := by
  have lower := first_complete_loss_persists pulse runtimeSeed 2 depth Pulse.clockTask decoder
  dsimp only at lower
  rw [Pulse.actor_loss_sixth, Pulse.field_loss_half] at lower
  norm_num at lower
  exact lower

theorem pulse_constant_one (depth : Nat) :
    rawTerminalError pulse runtimeSeed 2 depth (Clock.task 2) (fun _ => 1) = (2 / 3 : ℝ) :=
  Pulse.constant_one_attains

theorem complete_pulse_floor (depth : Nat) :
    let value := taskValue (historyPMF 2) (Clock.task 2)
    ‖actorResidual pulse runtimeSeed 2 value‖ ^ 2 +
        SourceGeneratedEmpiricalHilbert.inventoryEnergy pulse runtimeSeed 2 (depth + 1)
          (SourceGeneratedEmpiricalHilbert.retainedHistory pulse runtimeSeed 2 (depth + 1)
            (actorTransfer pulse runtimeSeed 2 value)).2 = (2 / 3 : ℝ) := by
  have lower := pulse_cost_lower depth (fun atom =>
    (SourceGeneratedEmpiricalHilbert.retainedHistory pulse runtimeSeed 2 (depth + 1)
      (actorTransfer pulse runtimeSeed 2 (taskValue (historyPMF 2) (Clock.task 2)))).1 atom)
  exact le_antisymm
    ((complete_error_lower_bound pulse runtimeSeed 2 depth (Clock.task 2) (fun _ => 1)).trans_eq (pulse_constant_one depth))
    (lower.trans_eq (complete_error_attains pulse runtimeSeed 2 depth (Clock.task 2)))

theorem same_source_recovery (depth : Nat) (decoder : Field (process := process) pulse → ℂ) :
    error (historyPMF 2) (Clock.observe 2 depth) (Clock.task 2) (Clock.decode depth) = 0 ∧
      (2 / 3 : ℝ) ≤ rawTerminalError pulse runtimeSeed 2 depth (Clock.task 2) decoder :=
  ⟨Clock.exact_recovery_cost 2 depth, pulse_cost_lower depth decoder⟩

end
end SourceWeightedRecovery.Runtime.Actor.History.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
