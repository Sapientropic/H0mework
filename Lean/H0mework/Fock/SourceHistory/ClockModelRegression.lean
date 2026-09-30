import H0mework.Fock.SourceHistoryClock.Fock

/-! Two actual adjacent source points share a cancelled current clock but expose mass in the next reading. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockModel.Controls

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceSuccessorBoundary

noncomputable section

def hiddenWord (depth : Nat) : Nat →₀ ℤ :=
  rawClock (runtimeAt depth).tick.next.state • SourceOperationNative.point (runtimeAt depth) -
    rawClock (runtimeAt depth).state • SourceOperationNative.point (runtimeAt depth).tick.next

theorem hidden_clock (depth : Nat) : clock (hiddenWord depth) = 0 := by
  simp only [hiddenWord, map_sub, map_smul]
  simp only [SourceOperationNative.point, SourceOperationNative.statePoint, clock_single, one_mul, smul_eq_mul]
  change rawClock (runtimeAt depth).tick.next.state * rawClock (runtimeAt depth).state -
    rawClock (runtimeAt depth).state * rawClock (runtimeAt depth).tick.next.state = 0
  ring

theorem hidden_mass (depth : Nat) : mass ℤ (hiddenWord depth) = 1 := by
  simp only [hiddenWord, map_sub, map_smul]
  simp only [SourceOperationNative.point, SourceOperationNative.statePoint, mass_single, smul_eq_mul, mul_one]
  change (((runtimeAt depth).state + 1 : Nat) : ℤ) + 1 - ((runtimeAt depth).state + 1 : ℤ) = 1
  simp

theorem next_clock_exposes_mass (depth : Nat) : clock (push ℤ (hiddenWord depth)) = 1 := by
  rw [clock_push, hidden_clock, hidden_mass, zero_add]

theorem same_current_clock (depth : Nat) : clockRead (projection (hiddenWord depth)) = clockRead 0 := by
  rw [clockRead_source, hidden_clock, map_zero]

theorem different_model (depth : Nat) : projection (hiddenWord depth) ≠ 0 := by
  intro merged
  have observed := massRead_source (hiddenWord depth)
  rw [merged, map_zero, hidden_mass] at observed
  exact zero_ne_one observed

theorem next_model_clock_differs (depth : Nat) :
    clockRead (action (projection (hiddenWord depth))) ≠ clockRead (action 0) := by
  rw [action_source, clockRead_source, next_clock_exposes_mass, map_zero, map_zero]
  exact one_ne_zero

end
end SourceClockModel.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
