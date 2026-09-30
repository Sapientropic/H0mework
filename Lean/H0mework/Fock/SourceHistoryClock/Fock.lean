import H0mework.Fock.SourceHistoryClock.Model
import H0mework.Fock.SourceHistory.Installed

/-! The existing native model point reads the original current's clock and actual next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockModel.Fock

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceOwnedObservationHistory.Installed

noncomputable section

def point (depth : Nat) : Model :=
  SourceOperationNative.Observed.modelPoint (process := process) rawClock (runtimeAt depth)

theorem rawClock_current (depth : Nat) :
    rawClock (runtimeAt depth).state = (scanIndex (runtimeAt depth).current.visit.current : ℤ) := by
  rw [runtimeAt_state, runtimeAt_scanIndex]
  simp only [rawClock, Nat.cast_add, Nat.cast_one]

theorem clock_current (depth : Nat) : clockRead (point depth) = (scanIndex (runtimeAt depth).current.visit.current : ℤ) :=
  (SourceOperationNative.Observed.modelPoint_read (process := process) rawClock (runtimeAt depth)).trans
    (rawClock_current depth)

theorem mass_current (depth : Nat) : massRead (point depth) = 1 := by
  change massRead (projection (SourceOperationNative.point (runtimeAt depth))) = 1
  rw [massRead_source]
  exact SourceSuccessorBoundary.mass_single ℤ (runtimeAt depth).state 1

theorem point_next (depth : Nat) : action (point depth) = point (depth + 1) :=
  SourceOperationNative.Observed.modelAction_point (process := process) rawClock (runtimeAt depth)

theorem clock_native_target (depth : Nat) :
    clockRead (action (point depth)) = (scanIndex (runtimePayload depth).nativeWrite.target : ℤ) := by
  rw [point_next]
  have target := clock_current (depth + 1)
  exact target.trans (congrArg (fun current => (scanIndex current : ℤ)) (runtime_current_next depth))

end
end SourceClockModel.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
