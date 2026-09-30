import H0mework.Fock.SourceHistoryClock.BinomialInstalled

/-! The new source moment supplies a linear decoder for the original historical square task. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceWeightedRecovery

noncomputable section

private theorem generatedAdvance (first second : Nat) :
    (runtimeSeed.advance first).advance second = runtimeAt (first + second) := by
  induction second with
  | zero => rfl
  | succ second previous =>
      exact congrArg (fun runtime : LivingRuntimeState process => runtime.tick.next) previous

def futureModel (bound depth : Nat) (index : Fin (bound + 1)) : Model :=
  SourceOperationNative.Observed.modelPoint (process := process) rawSecond
    ((history (runtimeSeed.advance depth) bound).stageAt index).next

theorem futureModel_source (bound depth : Nat) (index : Fin (bound + 1)) :
    futureModel bound depth index = Fock.point (index.val + (depth + 1)) := by
  have actual := congrArg (fun runtime : LivingRuntimeState process => runtime.tick.next)
    (generatedAdvance depth index.val)
  have point := congrArg (SourceOperationNative.Observed.modelPoint (process := process) rawSecond) actual
  have next : SourceOperationNative.Observed.modelPoint (process := process) rawSecond
      (runtimeAt (depth + index.val)).tick.next = Fock.point (depth + index.val + 1) := rfl
  exact point.trans (next.trans (congrArg Fock.point
    (by omega : depth + index.val + 1 = index.val + (depth + 1))))

theorem forget_futureModel (bound depth : Nat) (index : Fin (bound + 1)) :
    forgetClock (futureModel bound depth index) = Runtime.Actor.History.Clock.futureModel bound depth index :=
  forget_source (SourceOperationNative.point ((history (runtimeSeed.advance depth) bound).stageAt index).next)

theorem linear_recovers_source (bound depth : Nat) (index : Fin (bound + 1)) :
    (pastSquare (depth + 1) (futureModel bound depth index) : ℂ) = Runtime.Actor.History.Clock.sourceSquare bound index := by
  rw [futureModel_source]
  exact Controls.source_square_linear_recovery bound depth index

theorem exact_square_cost (bound depth : Nat) :
    error (historyPMF bound) (futureModel bound depth) (Runtime.Actor.History.Clock.sourceSquare bound)
      (fun value => (pastSquare (depth + 1) value : ℂ)) = 0 := by
  simp only [error, linear_recovers_source, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
