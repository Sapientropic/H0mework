import H0mework.Versions.X.Arithmetic.GoldbachDynamics.Runtime
import H0mework.Versions.X.Arithmetic.FockState.PrimePairOccupation

/-!
# Runtime prime-pair occupation readback

The operational Goldbach current and the particle--wave payload already share
one emitted root occurrence.  This module reads the exact even-charge atomic
occupation from that payload's source-generated Fock state and identifies it
with the existing additive coefficient at the runtime-owned scan index.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockRuntimePrimePairOccupation

open CanonicalUnitArithmeticEffectiveAdditiveCoefficientProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open ParticleWaveFock

noncomputable section

theorem runtimeAtomicOccupation_eq_generatedAdditiveCoefficient
    (depth : Nat) :
    let current := (runtimeAt depth).current.visit.current
    atomicTargetAmplitude (scanIndex current)
        (runtimeParticleWavePayload depth).sourceState =
      (generatedAdditiveCoefficient (scanIndex current) : ℤ) := by
  dsimp only
  rw [(runtimeParticleWavePayload depth).sourceState_eq]
  change atomicPrimePairOccupation
      (ParticleWaveFockRuntime.liveGlobalOwner
        (runtimeAt depth).current.visit.current)
      (scanIndex (runtimeAt depth).current.visit.current) = _
  exact atomicPrimePairOccupation_eq_generatedAdditiveCoefficient _ _

theorem runtimeAtomicOccupation_ne_zero_iff_coefficient_pos
    (depth : Nat) :
    let current := (runtimeAt depth).current.visit.current
    atomicTargetAmplitude (scanIndex current)
        (runtimeParticleWavePayload depth).sourceState ≠ 0 ↔
      0 < generatedAdditiveCoefficient (scanIndex current) := by
  dsimp only
  rw [runtimeAtomicOccupation_eq_generatedAdditiveCoefficient]
  omega

theorem runtimeAtomicOccupation_ne_zero_iff_effectiveFibre
    (depth : Nat) :
    let current := (runtimeAt depth).current.visit.current
    atomicTargetAmplitude (scanIndex current)
        (runtimeParticleWavePayload depth).sourceState ≠ 0 ↔
      Nonempty (CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveFibreAt
        (scanIndex current)) := by
  dsimp only
  rw [(runtimeParticleWavePayload depth).sourceState_eq]
  change atomicPrimePairOccupation
      (ParticleWaveFockRuntime.liveGlobalOwner
        (runtimeAt depth).current.visit.current)
      (scanIndex (runtimeAt depth).current.visit.current) ≠ 0 ↔ _
  exact atomicPrimePairOccupation_ne_zero_iff_effectiveFibre _ _

end

end ParticleWaveFockRuntimePrimePairOccupation
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
