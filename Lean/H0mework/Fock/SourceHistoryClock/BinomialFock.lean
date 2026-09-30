import H0mework.Fock.SourceHistoryClock.BinomialFibre

/-! The same original native actors generate the new moment point and its actual action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Fock

open SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def point (depth : Nat) : Model :=
  SourceOperationNative.Observed.modelPoint (process := process) rawSecond (runtimeAt depth)

theorem point_next (depth : Nat) : action (point depth) = point (depth + 1) :=
  SourceOperationNative.Observed.modelAction_point (process := process) rawSecond (runtimeAt depth)

theorem second_point (depth : Nat) : secondRead (point depth) = rawSecond depth :=
  (SourceOperationNative.Observed.modelPoint_read (process := process) rawSecond (runtimeAt depth)).trans
    (congrArg rawSecond (runtimeAt_state depth))

theorem clock_point (depth : Nat) : clockRead (point depth) = (depth : ℤ) + 1 := by
  change clockRead (projection (SourceOperationNative.point (runtimeAt depth))) = _
  rw [clockRead_source]
  change SourceClockModel.clock (Finsupp.single (runtimeAt depth).state 1) = _
  rw [SourceClockModel.clock_single, one_mul, runtimeAt_state]

theorem mass_point (depth : Nat) : massRead (point depth) = 1 := by
  change massRead (projection (SourceOperationNative.point (runtimeAt depth))) = 1
  rw [massRead_source]
  exact mass_single ℤ (runtimeAt depth).state 1

theorem square_point (depth : Nat) : squareRead (point depth) = (depth : ℤ) ^ 2 := by
  change 2 * secondRead (point depth) - clockRead (point depth) + massRead (point depth) = _
  rw [second_point, clock_point, mass_point]
  exact (source_square depth).symm

end
end SourceBinomialClock.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
