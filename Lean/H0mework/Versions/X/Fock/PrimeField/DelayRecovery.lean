import H0mework.Versions.X.Fock.PrimeField.DelayInformation

/-! The same complete Model and weights preserve recovery while the finite query retains its actual loss. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationDelay

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalTransfer SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

local instance : UniformSpace (Field (process := process) rawField) := fieldUniform (process := process) rawField
local instance : MeasurableSpace (Field (process := process) rawField) := fieldBorel (process := process) rawField
local instance : BorelSpace (Field (process := process) rawField) := ⟨rfl⟩
local instance : T2Space (Field (process := process) rawField) := field_t2 (process := process) rawField

theorem full_next_injective (owner : GlobalParentOwner) (runtime : LivingRuntimeState process) (bound : Nat) :
    Function.Injective (nextAtom (process := process) rawField runtime bound) := by
  intro left right same
  have models := (SourceConditionalRecovery.nextAtom_model_iff (process := process) rawField runtime bound left right).mp same
  have words := (original_model_fibre owner (SourceOperationNative.point ((history runtime bound).stageAt left).next)
    (SourceOperationNative.point ((history runtime bound).stageAt right).next)).mp models
  have states := SourceOperationNative.statePoint_injective process words
  change (runtime.advance left.val).state + 1 = (runtime.advance right.val).state + 1 at states
  rw [native_state_advance, native_state_advance] at states
  exact Fin.ext (Nat.add_left_cancel (Nat.add_right_cancel states))

theorem complete_recovers (owner : GlobalParentOwner) (runtime : LivingRuntimeState process) (bound : Nat)
    (task : Fin (bound + 1) → ℂ) (index : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtime bound
        (Runtime.Actor.actorTransfer (process := process) rawField runtime bound (taskValue (historyPMF bound) task))
        (nextAtom (process := process) rawField runtime bound index) = task index :=
  (Runtime.Actor.completeTransfer_is_conditional (process := process) rawField runtime bound task
    (nextAtom (process := process) rawField runtime bound index)).trans
    (ObservationRefinement.optimum_injective (historyPMF bound) (nextAtom (process := process) rawField runtime bound)
      (full_next_injective owner runtime bound) task index (by simp [historyPMF]))

theorem residuals_zero (owner : GlobalParentOwner) (runtime : LivingRuntimeState process) (bound : Nat)
    (task : Fin (bound + 1) → ℂ) :
    let value := taskValue (historyPMF bound) task
    Runtime.Actor.actorResidual (process := process) rawField runtime bound value = 0 ∧
      SourceGeneratedEmpiricalHilbert.residual (process := process) rawField runtime bound
        (Runtime.Actor.actorTransfer (process := process) rawField runtime bound value) = 0 := by
  dsimp only
  have energy := Runtime.Actor.rawError_attains (process := process) rawField runtime bound task
  dsimp only at energy
  simp only [Runtime.Actor.rawError, error, complete_recovers owner runtime, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero] at energy
  constructor
  · apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖SourceGeneratedEmpiricalHilbert.residual (process := process) rawField runtime bound
      (Runtime.Actor.actorTransfer (process := process) rawField runtime bound (taskValue (historyPMF bound) task))‖]
  · apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖Runtime.Actor.actorResidual (process := process) rawField runtime bound (taskValue (historyPMF bound) task)‖]

end
end SourcePrimeObservationDelay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
