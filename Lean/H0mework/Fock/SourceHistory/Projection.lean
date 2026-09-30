import H0mework.Probability.SourceProjection.Readout
import H0mework.Fock.SourceHistory.Installed

/-! The original particle, wave and joint readouts are generated restrictions of one full native field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullProjection.Fock

open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

def stateProjection : Field nativeStep fullRead →ₗ[ℤ] ParentCarrier :=
  readNow nativeStep sourceStateAt

def waveProjection : Field nativeStep fullRead →ₗ[ℤ] ColoredWaveOne :=
  (LinearMap.fst ℤ _ _).comp stateProjection

def particleProjection : Field nativeStep fullRead →ₗ[ℤ] OrderedParticleTwo :=
  (LinearMap.snd ℤ _ _).comp stateProjection

def jointProjection : Field nativeStep fullRead →ₗ[ℤ] JointMeasurementTarget :=
  jointMeasurement.comp stateProjection

theorem wave_particle_same_source (value : Field nativeStep fullRead) :
    (waveProjection value, particleProjection value) = stateProjection value := rfl

variable {current : Current}
variable {occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
variable {active : 1 ≤ scanIndex current}
variable (payload : RootGeneratedParticleWaveCurrentAt current occurrence active)

theorem stateProjection_source : stateProjection (fieldPoint nativeStep fullRead current) = payload.sourceState :=
  (readNow_point nativeStep sourceStateAt current).trans payload.sourceState_eq.symm

theorem stateProjection_target :
    stateProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current)) = payload.targetState := by
  rw [native_field_point payload]
  change readNow nativeStep sourceStateAt (fieldPoint nativeStep fullRead payload.nativeWrite.target) = _
  rw [readNow_point, payload.nativeWrite_eq]
  exact payload.targetState_eq.symm

theorem stateProjection_effect :
    stateProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current)) =
      stateProjection (fieldPoint nativeStep fullRead current) + payload.forcedTrace := by
  rw [stateProjection_source payload, stateProjection_target payload]
  exact payload.stateUpdate

theorem waveProjection_target :
    waveProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current)) = payload.targetState.1 :=
  congrArg Prod.fst (stateProjection_target payload)

theorem particleProjection_target :
    particleProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current)) = payload.targetState.2 :=
  congrArg Prod.snd (stateProjection_target payload)

theorem jointProjection_effect :
    jointProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current)) =
      jointProjection (fieldPoint nativeStep fullRead current) + jointMeasurement payload.forcedTrace := by
  change jointMeasurement (stateProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current))) = _
  rw [stateProjection_effect payload, map_add]
  rfl

include payload in
theorem inverse_fibre (alternative : ParentCarrier) :
    jointMeasurement alternative =
        jointProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current)) ↔
      alternative - stateProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current)) ∈
        JointMeasurementKernel := by
  change jointMeasurement alternative =
      jointMeasurement (stateProjection (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead current))) ↔ _
  rw [stateProjection_target payload]
  exact payload.inverseFibreLaw alternative

end
end SourceOwnedObservationHistory.FullProjection.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
