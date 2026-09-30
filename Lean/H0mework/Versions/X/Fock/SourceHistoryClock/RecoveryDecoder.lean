import H0mework.Probability.EmpiricalRecovery.ActorHistoryError
import H0mework.Versions.X.Fock.SourceHistoryClock.FrameAction

/-! The already generated clock frame and action inverse recover the same original actor task. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Clock

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

private theorem generatedAdvance (first second : Nat) :
    (runtimeSeed.advance first).advance second = runtimeAt (first + second) := by
  induction second with
  | zero => rfl
  | succ second previous =>
      exact congrArg (fun runtime : LivingRuntimeState process => runtime.tick.next) previous

def futureModel (bound depth : Nat) (index : Fin (bound + 1)) : SourceClockModel.Model :=
  SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock
    ((history (runtimeSeed.advance depth) bound).stageAt index).next

theorem futureModel_source (bound depth : Nat) (index : Fin (bound + 1)) :
    futureModel bound depth index = SourceClockModel.Fock.point (index.val + (depth + 1)) := by
  have actual := congrArg (fun runtime : LivingRuntimeState process => runtime.tick.next)
    (generatedAdvance depth index.val)
  have point := congrArg (SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock) actual
  have next : SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock
      (runtimeAt (depth + index.val)).tick.next = SourceClockModel.Fock.point (depth + index.val + 1) := rfl
  exact point.trans (next.trans (congrArg SourceClockModel.Fock.point
    (by omega : depth + index.val + 1 = index.val + (depth + 1))))

theorem undo_actual_steps (steps first : Nat) :
    (SourceClockFrame.inverse 0 ^ steps) (SourceClockModel.Fock.point (first + steps)) =
      SourceClockModel.Fock.point first := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
      rw [pow_succ]
      change (SourceClockFrame.inverse 0 ^ steps)
        (SourceClockFrame.inverse 0 (SourceClockModel.Fock.point (first + steps + 1))) = _
      rw [← SourceClockModel.Fock.point_next, SourceClockFrame.inverse_action]
      exact previous

def observe (bound depth : Nat) (index : Fin (bound + 1)) : ℤ × ℤ :=
  SourceClockFrame.coordinates 0 (futureModel bound depth index)

def decode (depth : Nat) (coordinates : ℤ × ℤ) : ℂ :=
  let recovered := (SourceClockFrame.inverse 0 ^ (depth + 1)) (SourceClockFrame.rebuild 0 coordinates)
  ((SourceClockModel.clockRead recovered - SourceClockModel.massRead recovered : ℤ) : ℂ)

def task (bound : Nat) (index : Fin (bound + 1)) : ℂ := (sample runtimeSeed bound index : Nat)

theorem task_source (bound : Nat) (index : Fin (bound + 1)) : task bound index = (index.val : ℂ) :=
  congrArg (fun state : Nat => (state : ℂ)) (runtimeAt_state index.val)

theorem decoded_model (bound depth : Nat) (index : Fin (bound + 1)) :
    (SourceClockFrame.inverse 0 ^ (depth + 1)) (SourceClockFrame.rebuild 0 (observe bound depth index)) =
      SourceClockModel.Fock.point index.val := by
  rw [observe, SourceClockFrame.rebuild_coordinates, futureModel_source, undo_actual_steps]

theorem recovers_actor (bound depth : Nat) (index : Fin (bound + 1)) :
    decode depth (observe bound depth index) = task bound index := by
  rw [decode, decoded_model, SourceClockModel.Fock.clock_current, SourceClockModel.Fock.mass_current,
    runtimeAt_scanIndex, task_source]
  push_cast
  ring

theorem exact_recovery_cost (bound depth : Nat) :
    error (historyPMF bound) (observe bound depth) (task bound) (decode depth) = 0 := by
  simp only [error, recovers_actor, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

end
end SourceWeightedRecovery.Runtime.Actor.History.Clock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
