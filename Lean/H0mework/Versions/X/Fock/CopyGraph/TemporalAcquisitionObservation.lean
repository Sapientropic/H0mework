import H0mework.Versions.X.Fock.CopyGraph.TemporalAcquisitionModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalAcquisition

open SourceCopyProgram (Index sourceDepth)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyTemporalBoundary.normal_consumed runtime index) ∧
      ∀ material : Index (inventoryBound (next runtime)),
        type_of% (newest_boundary_closed runtime material) ∧ type_of% (newest_boundary_decreases runtime material) ∧
        type_of% (newest_birth_coordinate runtime material) ∧ type_of% (newest_birth_cost runtime material) ∧
        type_of% (SourceCopyTemporalBoundary.newest_input_energy runtime material) := by
  with_reducible exact ⟨SourceCopyTemporalBoundary.normal_consumed runtime index,
    fun material => ⟨newest_boundary_closed runtime material, newest_boundary_decreases runtime material,
      newest_birth_coordinate runtime material, newest_birth_cost runtime material,
      SourceCopyTemporalBoundary.newest_input_energy runtime material⟩⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyTemporalBoundary.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      ∀ steps : Nat,
        (∀ target : SourceJointClockGraph.Carrier,
          type_of% (observer_step runtime index steps target) ∧ type_of% (boundary_step runtime index steps target)) ∧
        ∀ value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps),
          type_of% (material_consumed runtime index steps value) ∧
          type_of% (retained_birth_zero runtime index steps value) ∧ type_of% (boundary_birth runtime index steps value)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCopyTemporalBoundary.observation_consumed runtime index, normal_consumed runtime index,
    fun steps => ⟨fun target => ⟨observer_step runtime index steps target, boundary_step runtime index steps target⟩,
      fun value => ⟨material_consumed runtime index steps value, retained_birth_zero runtime index steps value,
        boundary_birth runtime index steps value⟩⟩⟩

def ActualRecovery : Prop :=
    SourceCopyTemporalBoundary.ActualRecovery ∧
      ∀ runtime : LivingRuntimeState process, ∀ index : Index (inventoryBound (next runtime)),
        type_of% (newest_boundary_closed runtime index) ∧ type_of% (newest_boundary_decreases runtime index) ∧
        type_of% (newest_birth_coordinate runtime index) ∧ type_of% (newest_birth_cost runtime index)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCopyTemporalBoundary.actual_recovery_consumed,
    fun runtime index => ⟨newest_boundary_closed runtime index, newest_boundary_decreases runtime index,
      newest_birth_coordinate runtime index, newest_birth_cost runtime index⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyTemporalBoundary.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyTemporalBoundary.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyTemporalAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
