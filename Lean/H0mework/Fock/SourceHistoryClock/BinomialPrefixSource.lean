import H0mework.Fock.SourceHistory.ClockPrefixRegression
import H0mework.Fock.SourceHistoryClock.BinomialRecovery

/-! The raw prefix is read from the same three actual actor next snapshots, before model recovery. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Prefix

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem iterate_source (steps : Nat) (word : Nat →₀ ℤ) :
    (action ^ steps) (projection word) = projection ((SourceClockModel.nativeAction ^ steps) word) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
      rw [pow_succ', pow_succ']
      change action ((action ^ steps) (projection word)) =
        projection (SourceClockModel.nativeAction ((SourceClockModel.nativeAction ^ steps) word))
      rw [previous]
      exact action_source _

theorem window_source (word : Nat →₀ ℤ) :
    window (projection word) = SourceGeneratedActionObservationHistory.prefixEvaluator SourceClockModel.nativeAction second 2 word := by
  funext index
  change secondRead ((action ^ index.val) (projection word)) = second ((SourceClockModel.nativeAction ^ index.val) word)
  rw [iterate_source, secondRead_source]

theorem iterate_point (first steps : Nat) :
    (action ^ steps) (Fock.point first) = Fock.point (first + steps) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
      rw [pow_succ']
      change action ((action ^ steps) (Fock.point first)) = _
      rw [previous, Fock.point_next, Nat.add_assoc]

def currentSamples (depth : Nat) : Window := fun index =>
  rawSecond (sample (runtimeSeed.advance depth) 2 index)

theorem currentSamples_window (depth : Nat) : currentSamples depth = window (Fock.point depth) := by
  symm
  change window (projection (SourceOperationNative.point (runtimeAt depth))) = _
  rw [window_source]
  funext index
  change second ((SourceClockModel.nativeAction ^ index.val) (SourceOperationNative.point (runtimeAt depth))) =
    rawSecond ((runtimeAt depth).advance index.val).state
  rw [SourceOperationNative.Observed.sourceAction_pow_point]
  exact SourceOperationNative.observer_point rawSecond ((runtimeAt depth).advance index.val)

def samples (depth : Nat) : Window := fun index =>
  rawSecond (((history (runtimeSeed.advance depth) 2).stageAt index).next.state)

theorem samples_are_actual (depth : Nat) (index : Fin 3) :
    samples depth index = secondRead (futureModel 2 depth index) :=
  (SourceOperationNative.Observed.modelPoint_read (process := process) rawSecond
    ((history (runtimeSeed.advance depth) 2).stageAt index).next).symm

theorem samples_window (depth : Nat) : samples depth = window (Fock.point (depth + 1)) := by
  funext index
  rw [samples_are_actual, futureModel_source]
  change secondRead (Fock.point (index.val + (depth + 1))) = secondRead ((action ^ index.val) (Fock.point (depth + 1)))
  rw [iterate_point, Nat.add_comm]

theorem next_samples (depth : Nat) : next (currentSamples depth) = samples depth := by
  rw [currentSamples_window, next_window, Fock.point_next, samples_window]

theorem recovered_original (depth : Nat) : recover (samples depth) = Fock.point (depth + 1) := by
  rw [samples_window, recover_window]

theorem reconstructs_actual_actor (depth : Nat) (index : Fin 3) :
    (action ^ index.val) (recover (samples depth)) = futureModel 2 depth index := by
  rw [recovered_original, iterate_point, futureModel_source, Nat.add_comm]

theorem source_square_from_samples (depth : Nat) (index : Fin 3) :
    (pastSquare (depth + 1) ((action ^ index.val) (recover (samples depth))) : ℂ) =
      SourceWeightedRecovery.Runtime.Actor.History.Clock.sourceSquare 2 index := by
  rw [reconstructs_actual_actor]
  exact linear_recovers_source 2 depth index

end
end SourceBinomialClock.Prefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
