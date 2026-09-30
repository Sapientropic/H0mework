import H0mework.Versions.X.Fock.PrimeField.ClockResidualConsumer

/-! The original clock read fixes a linear source correction without altering its paid prime prefix. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeClockResidual

noncomputable section

def correction (stage : Nat) : SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
  LinearMap.id - SourceClockModel.clock.smulRight (word stage)

theorem correction_apply (stage : Nat) (source : SourceOperationNative.Carrier process) :
    correction stage source = source - SourceClockModel.clock source • word stage := rfl

theorem corrected_mass (stage : Nat) (source : SourceOperationNative.Carrier process) :
    SourceSuccessorBoundary.mass ℤ (correction stage source) = SourceSuccessorBoundary.mass ℤ source := by
  rw [correction_apply, map_sub, map_smul, mass_zero, smul_zero, sub_zero]

theorem corrected_clock (stage : Nat) (source : SourceOperationNative.Carrier process) :
    SourceClockModel.clock (correction stage source) = 0 := by
  rw [correction_apply, map_sub, map_smul, clock_unit, smul_eq_mul, mul_one, sub_self]

theorem corrected_prime (bound stage : Nat) (inside : stage ≤ bound) (source : SourceOperationNative.Carrier process) :
    observation ((nativeAction ^ stage) (correction bound source)) = observation ((nativeAction ^ stage) source) := by
  rw [correction_apply, map_sub, map_smul, map_sub, map_smul,
    prime_prefix_zero bound stage inside, smul_zero, sub_zero]

theorem corrected_prefix (bound stage : Nat) (inside : stage ≤ bound) (source : SourceOperationNative.Carrier process) :
    prefixEvaluator nativeAction jointObservation stage (correction bound source) =
      fun index => (observation ((nativeAction ^ index.val) source), (index.val : ℤ) * SourceSuccessorBoundary.mass ℤ source) := by
  funext index
  change jointObservation ((nativeAction ^ index.val) (correction bound source)) = _
  rw [observation_joint]
  change (observation ((nativeAction ^ index.val) (correction bound source)),
    SourceClockModel.clock ((SourceSuccessorBoundary.push ℤ ^ index.val) (correction bound source))) = _
  rw [corrected_prime bound index.val (by omega), SourceClockModel.clock_pow, corrected_clock, corrected_mass, zero_add]

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
