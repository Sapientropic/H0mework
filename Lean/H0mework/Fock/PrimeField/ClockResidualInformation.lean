import H0mework.Fock.PrimeField.ClockResidualQuery

/-! The actual clock face supplies the original prime-field conditional and transfer on the same actor history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalTransfer SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

local instance : UniformSpace (Field (process := process) rawField) := fieldUniform (process := process) rawField
local instance : MeasurableSpace (Field (process := process) rawField) := fieldBorel (process := process) rawField
local instance : BorelSpace (Field (process := process) rawField) := ⟨rfl⟩
local instance : T2Space (Field (process := process) rawField) := field_t2 (process := process) rawField

theorem conditional_pure (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    FiniteRecurrence.Native.conditional (process := process) jointRead 0 current bound actor = PMF.pure actor :=
  ObservationRefinement.conditional_injective (historyPMF bound) (observe current bound)
    (observe_injective current bound) actor (by simp [historyPMF])

theorem conditional_is_original (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    FiniteRecurrence.Native.conditional (process := process) jointRead 0 current bound actor =
      conditionalIndices (process := process) rawField current bound (nextAtom (process := process) rawField current bound actor)
        (SourceConditionalRecovery.nextAtom_supported (process := process) rawField current bound actor) := by
  have original := ObservationRefinement.conditional_injective (historyPMF bound)
    (nextAtom (process := process) rawField current bound)
    (SourcePrimeObservationDelay.full_next_injective sourceOwner current bound) actor (by simp [historyPMF])
  exact (conditional_pure current bound actor).trans original.symm

theorem transfer_from_joint_conditional (current : LivingRuntimeState process) (bound : Nat)
    (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField current bound
      (Runtime.Actor.actorTransfer (process := process) rawField current bound (taskValue (historyPMF bound) task))
      (nextAtom (process := process) rawField current bound actor) =
      ∑ candidate : Fin (bound + 1),
        (FiniteRecurrence.Native.conditional (process := process) jointRead 0 current bound actor candidate).toReal • task candidate := by
  rw [conditional_is_original]
  exact (Runtime.Actor.completeTransfer_is_conditional (process := process) rawField current bound task
    (nextAtom (process := process) rawField current bound actor)).trans
    (optimal_is_conditional (historyPMF bound) (nextAtom (process := process) rawField current bound) task
      (nextAtom (process := process) rawField current bound actor) (by
        change nextAtom (process := process) rawField current bound actor ∈
          ((historyPMF bound).map (nextAtom (process := process) rawField current bound)).support
        rw [← nextPMF_from_indices]
        exact SourceConditionalRecovery.nextAtom_supported (process := process) rawField current bound actor))

theorem clock_cost_zero (current : LivingRuntimeState process) (bound : Nat) :
    error (historyPMF bound) (observe current bound) (fun actor => (sample current bound actor : Nat)) decodeClock = 0 := by
  simp only [error, clock_recovered, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

theorem original_transfer_clock (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField current bound
      (Runtime.Actor.actorTransfer (process := process) rawField current bound
        (taskValue (historyPMF bound) (fun actor => (sample current bound actor : Nat))))
      (nextAtom (process := process) rawField current bound actor) = decodeClock (observe current bound actor) := by
  rw [clock_recovered]
  exact SourcePrimeObservationDelay.complete_recovers sourceOwner current bound _ actor

theorem prime_loss_joint_recovery (bound width : Nat) :
    let current := SourcePrimeObservationDelay.startRuntime sourceOwner bound width
    SourceWeightedRecovery.error (historyPMF bound) (SourcePrimeObservationDelay.shortQuery sourceOwner bound width)
        (SourcePrimeObservationDelay.clockTask sourceOwner bound width)
        (fun _ => (((SourcePrimeObservationDelay.firstState sourceOwner (bound + width) : ℝ) + bound / 2 : ℝ) : ℂ)) -
      error (historyPMF bound) (observe current bound) (SourcePrimeObservationDelay.clockTask sourceOwner bound width) decodeClock =
        (bound : ℝ) * (bound + 2) / 12 := by
  dsimp only
  rw [SourcePrimeObservationDelay.minimum_clock_cost]
  have zero : error (historyPMF bound)
      (observe (SourcePrimeObservationDelay.startRuntime sourceOwner bound width) bound)
      (SourcePrimeObservationDelay.clockTask sourceOwner bound width) decodeClock = 0 :=
    clock_cost_zero (SourcePrimeObservationDelay.startRuntime sourceOwner bound width) bound
  rw [zero, sub_zero]

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
