import H0mework.Versions.X.Fock.PrimeField.ClockResidualSource
import H0mework.Probability.Source.ModelJoint

/-! The already defined paired observation retains the original prime and clock reads of one source word. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

def jointRead : Nat → IntegralOneParticle × ℤ :=
  SourceOwnedObservationHistory.JointModel.pairRead rawField SourceClockModel.rawClock

abbrev jointObservation := SourceOperationNative.observer process jointRead

abbrev jointData := data nativeAction jointObservation

abbrev jointLaws := compatible nativeAction jointObservation

abbrev JointField := SourceGeneratedScalarCofinalTopology.NativeProbability.Field (process := process) jointRead

theorem observation_joint : jointObservation = observation.prod SourceClockModel.clock :=
  SourceOwnedObservationHistory.JointModel.observation_pair rawField SourceClockModel.rawClock

theorem joint_prefix (bound stage : Nat) (inside : stage ≤ bound) :
    prefixEvaluator nativeAction jointObservation stage (word bound) = fun _ => (0, 1) := by
  funext index
  change jointObservation ((nativeAction ^ index.val) (word bound)) = (0, 1)
  rw [observation_joint]
  change (observation ((nativeAction ^ index.val) (word bound)),
    SourceClockModel.clock ((nativeAction ^ index.val) (word bound))) = (0, 1)
  rw [prime_prefix_zero bound index.val (by omega), clock_prefix_unit]

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
