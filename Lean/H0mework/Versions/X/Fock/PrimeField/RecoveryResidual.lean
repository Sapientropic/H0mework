import H0mework.Versions.X.Fock.PrimeField.RecoveryInformation

/-! The original two residuals vanish only after the actual finite source query pays recovery. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

theorem residuals_zero (owner : GlobalParentOwner) (bound : Nat) (task : Fin (bound + 1) → ℂ) :
    let value := taskValue (historyPMF bound) task
    Runtime.Actor.actorResidual (process := process) rawField runtimeSeed bound value = 0 ∧
      SourceGeneratedEmpiricalHilbert.residual (process := process) rawField runtimeSeed bound
        (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound value) = 0 := by
  dsimp only
  have costs := Runtime.Actor.rawError_lower_bound (process := process) rawField runtimeSeed bound task
    (fun atom => decoder owner bound task (FiniteRecurrence.Native.fieldRead (process := process) rawField (windowBound owner bound) atom))
  dsimp only at costs
  rw [raw_error_zero] at costs
  constructor
  · apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖SourceGeneratedEmpiricalHilbert.residual (process := process) rawField runtimeSeed bound
      (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound (taskValue (historyPMF bound) task))‖]
  · apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖Runtime.Actor.actorResidual (process := process) rawField runtimeSeed bound
      (taskValue (historyPMF bound) task)‖]

theorem original_actor_reconstructed (owner : GlobalParentOwner) (bound : Nat) (task : Fin (bound + 1) → ℂ) :
    let value := taskValue (historyPMF bound) task
    Runtime.Actor.nextPullback (process := process) rawField runtimeSeed bound
      (SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed bound
        (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound value)) = value := by
  have whole := Runtime.Actor.reconstruct_actor (process := process) rawField runtimeSeed bound (taskValue (historyPMF bound) task)
  rw [(residuals_zero owner bound task).1, (residuals_zero owner bound task).2, map_zero, add_zero, add_zero] at whole
  exact whole

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
