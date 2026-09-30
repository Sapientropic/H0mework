import H0mework.Versions.X.Fock.PrimeField.DelayConsumer
import H0mework.Versions.X.Fock.SourceHistoryClock.Fock

/-! One actual native boundary keeps a clock unit while any prescribed finite prime prefix is silent. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

def start (bound : Nat) : Nat := SourcePrimeObservationDelay.firstState sourceOwner bound

def runtime (bound : Nat) : LivingRuntimeState process := runtimeAt (start bound)

def word (bound : Nat) : SourceOperationNative.Carrier process :=
  SourceSuccessorBoundary.boundary ℤ (SourceOperationNative.point (runtime bound))

theorem word_is_actual (bound : Nat) :
    word bound = SourceOperationNative.point (runtime bound).tick.next - SourceOperationNative.point (runtime bound) := by
  change SourceOperationNative.sourceAction process (SourceOperationNative.point (runtime bound)) -
    SourceOperationNative.point (runtime bound) = _
  rw [SourceOperationNative.sourceAction_point]

theorem word_is_source_boundary (bound : Nat) :
    word bound = SourceOperationNative.statePoint process (start bound + 1) -
      SourceOperationNative.statePoint process (start bound) := by
  calc
    _ = SourceSuccessorBoundary.boundary ℤ (SourceOperationNative.statePoint process (start bound)) :=
      congrArg (SourceSuccessorBoundary.boundary ℤ)
        (congrArg (SourceOperationNative.statePoint process) (runtimeAt_state (start bound)))
    _ = _ := SourceSuccessorBoundary.boundary_single ℤ (start bound) 1

theorem mass_zero (bound : Nat) : SourceSuccessorBoundary.mass ℤ (word bound) = 0 :=
  SourceSuccessorBoundary.mass_boundary ℤ _

theorem clock_unit (bound : Nat) : SourceClockModel.clock (word bound) = 1 := by
  change SourceClockModel.clock (SourceSuccessorBoundary.push ℤ (SourceOperationNative.point (runtime bound)) -
    SourceOperationNative.point (runtime bound)) = 1
  rw [map_sub, SourceClockModel.clock_push, add_sub_cancel_left]
  exact SourceSuccessorBoundary.mass_single ℤ (runtime bound).state 1

theorem prime_prefix_zero (bound stage : Nat) (inside : stage ≤ bound) :
    observation ((nativeAction ^ stage) (word bound)) = 0 := by
  rw [word_is_source_boundary, map_sub, map_sub, source_iterate, source_iterate,
    SourceOperationNative.observer_statePoint, SourceOperationNative.observer_statePoint]
  rw [show start bound + 1 + stage = start bound + stage + 1 by omega]
  change rawField (SourcePrimeObservationDelay.firstState sourceOwner bound + stage + 1) -
    rawField (SourcePrimeObservationDelay.firstState sourceOwner bound + stage) = 0
  rw [SourcePrimeObservationDelay.field_step sourceOwner bound stage inside, sub_self]

theorem clock_prefix_unit (bound stage : Nat) : SourceClockModel.clock ((nativeAction ^ stage) (word bound)) = 1 := by
  change SourceClockModel.clock ((SourceSuccessorBoundary.push ℤ ^ stage) (word bound)) = 1
  rw [SourceClockModel.clock_pow, clock_unit, mass_zero, mul_zero, add_zero]

theorem primitive_replays_source (bound : Nat) :
    SourceSuccessorBoundary.certificate ℤ (word bound) = SourceOperationNative.point (runtime bound) := by
  have actual := congrArg (SourceOperationNative.statePoint process) (runtimeAt_state (start bound))
  calc
    _ = SourceOperationNative.statePoint process (start bound) := by
      rw [word_is_source_boundary]
      change SourceSuccessorBoundary.certificate ℤ (Finsupp.single (start bound + 1) 1 - Finsupp.single (start bound) 1) = _
      rw [map_sub, SourceSuccessorBoundary.certificate_single, SourceSuccessorBoundary.certificate_single,
        one_smul, one_smul, Finset.sum_range_succ, add_sub_cancel_left]
      rfl
    _ = _ := actual.symm

theorem primitive_unit_mass (bound : Nat) : SourceSuccessorBoundary.mass ℤ (SourceSuccessorBoundary.certificate ℤ (word bound)) = 1 := by
  rw [primitive_replays_source]
  exact SourceSuccessorBoundary.mass_single ℤ (runtime bound).state 1

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
