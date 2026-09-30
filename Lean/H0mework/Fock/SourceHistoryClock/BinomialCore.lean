import H0mework.Fock.SourceHistoryClock.Model
import Mathlib.Data.Nat.Choose.Basic

/-! The original successor generates its next divided-power moment without inverting an integer unit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

open SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState

noncomputable section

def rawSecond (state : Nat) : ℤ := ((state + 1).choose 2 : ℤ)

abbrev second : (Nat →₀ ℤ) →ₗ[ℤ] ℤ :=
  SourceOperationNative.observer ParticleWaveFockRuntime.process rawSecond

theorem rawSecond_next (state : Nat) :
    rawSecond (state + 1) = rawSecond state + SourceClockModel.rawClock state := by
  have pascal := Nat.choose_succ_succ' (state + 1) 1
  simp only [Nat.choose_one_right] at pascal
  have casted := congrArg (fun value : Nat => (value : ℤ)) pascal
  simpa only [rawSecond, SourceClockModel.rawClock, Nat.cast_add, Nat.cast_one, add_comm] using casted

theorem second_single (state : Nat) (scalar : ℤ) :
    second (Finsupp.single state scalar) = scalar * rawSecond state := by
  simp [second, SourceOperationNative.observer]

theorem second_push (word : Nat →₀ ℤ) :
    second (push ℤ word) = second word + SourceClockModel.clock word := by
  have source := LinearMap.congr_fun
    (SourceOperationNative.observer_sourceAction (process := ParticleWaveFockRuntime.process) rawSecond) word
  change second (push ℤ word) = SourceOperationNative.observer ParticleWaveFockRuntime.process
    (fun state => rawSecond (state + 1)) word at source
  have observer : SourceOperationNative.observer ParticleWaveFockRuntime.process (fun state => rawSecond (state + 1)) =
      second + SourceClockModel.clock := by
    apply Finsupp.lhom_ext
    intro state scalar
    simp [second, SourceClockModel.clock, SourceOperationNative.observer, rawSecond_next, mul_add]
  exact source.trans (LinearMap.congr_fun observer word)

theorem source_square (state : Nat) :
    (state : ℤ) ^ 2 = 2 * rawSecond state - SourceClockModel.rawClock state + 1 := by
  induction state with
  | zero => norm_num [rawSecond, SourceClockModel.rawClock]
  | succ state previous =>
      rw [rawSecond_next]
      simp only [SourceClockModel.rawClock, Nat.cast_add, Nat.cast_one] at previous ⊢
      nlinarith only [previous]

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
