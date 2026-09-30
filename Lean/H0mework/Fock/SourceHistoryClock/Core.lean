import H0mework.Realization.Operations.SuccessorBoundary
import H0mework.Realization.Operations.ObservationNative
import H0mework.Arithmetic.FockDynamics.RootRuntime

/-! The original successor clock on complete words generates its mass increment. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockModel

open SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState

noncomputable section

def rawClock (state : Nat) : ℤ := (state : ℤ) + 1

abbrev clock : (Nat →₀ ℤ) →ₗ[ℤ] ℤ :=
  SourceOperationNative.observer ParticleWaveFockRuntime.process rawClock

theorem clock_single (index : Nat) (scalar : ℤ) :
    clock (Finsupp.single index scalar) = scalar * ((index : ℤ) + 1) := by
  simp [clock, SourceOperationNative.observer, rawClock]

theorem clock_push (word : Nat →₀ ℤ) : clock (push ℤ word) = clock word + mass ℤ word := by
  have sourceSquare := LinearMap.congr_fun
    (SourceOperationNative.observer_sourceAction (process := ParticleWaveFockRuntime.process) rawClock) word
  change clock (push ℤ word) =
    SourceOperationNative.observer ParticleWaveFockRuntime.process (fun state => rawClock (state + 1)) word
      at sourceSquare
  have nextObserver :
      SourceOperationNative.observer ParticleWaveFockRuntime.process (fun state => rawClock (state + 1)) =
        clock + mass ℤ := by
    apply Finsupp.lhom_ext
    intro index scalar
    simp [clock, SourceOperationNative.observer, mass, rawClock, mul_add, mul_two, add_assoc]
  exact sourceSquare.trans (LinearMap.congr_fun nextObserver word)

theorem clock_pow (stage : Nat) (word : Nat →₀ ℤ) :
    clock ((push ℤ ^ stage) word) = clock word + (stage : ℤ) * mass ℤ word := by
  induction stage generalizing word with
  | zero => simp
  | succ stage inductionHypothesis =>
      rw [pow_succ]
      change clock ((push ℤ ^ stage) (push ℤ word)) = _
      rw [inductionHypothesis, clock_push, mass_push]
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      abel

end
end SourceClockModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
