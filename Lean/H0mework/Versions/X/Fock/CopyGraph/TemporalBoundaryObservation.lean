import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundaryCofinal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalBoundary

open SourceCopyProgram (Index sourceDepth)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyTimeGram.normal_consumed runtime index) ∧
      (∀ target : SourceJointClockGraph.Carrier,
        type_of% (actual_model_next runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (boundary_residual runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (actual_model_next runtime index ((frontier runtime).stageCount + 2) target) ∧
        type_of% (boundary_residual runtime index ((frontier runtime).stageCount + 2) target)) ∧
      ∀ material : Index (inventoryBound (next runtime)),
        type_of% (newest_input_energy runtime material) ∧ type_of% (finite_next_missing_cost runtime material) := by
  with_reducible exact ⟨SourceCopyTimeGram.normal_consumed runtime index,
    fun target => ⟨actual_model_next runtime index _ target, boundary_residual runtime index _ target,
      actual_model_next runtime index _ target, boundary_residual runtime index _ target⟩,
    fun material => ⟨newest_input_energy runtime material, finite_next_missing_cost runtime material⟩⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyTimeGram.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      (∀ steps : Nat, type_of% (native_next runtime index steps) ∧ type_of% (native_decoder_next runtime index steps)) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (boundary_tendsto runtime index target) ∧
        ∀ steps : Nat, type_of% (actual_next runtime index steps target) ∧
          type_of% (finite_next runtime index steps target) ∧ type_of% (boundary_residual runtime index steps target) ∧
          type_of% (actual_decoder_next runtime index steps target) ∧ type_of% (actual_model_next runtime index steps target) ∧
          ∀ phase : Fin (index.val + 1 + 1), type_of% (prefix_native runtime index steps (index.val + 1) phase)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCopyTimeGram.observation_consumed runtime index, normal_consumed runtime index,
    fun steps => ⟨native_next runtime index steps, native_decoder_next runtime index steps⟩,
    fun target => ⟨boundary_tendsto runtime index target, fun steps => ⟨actual_next runtime index steps target,
      finite_next runtime index steps target, boundary_residual runtime index steps target,
      actual_decoder_next runtime index steps target, actual_model_next runtime index steps target,
      prefix_native runtime index steps (index.val + 1)⟩⟩⟩

def ActualRecovery : Prop :=
    SourceCopyTimeGram.ActualRecovery ∧
      ∀ runtime : LivingRuntimeState process, ∀ index : Index (inventoryBound (next runtime)),
        type_of% (newest_observed runtime index) ∧ type_of% (newest_time runtime index) ∧
        type_of% (boundary_coordinate runtime index) ∧ type_of% (boundary_nonzero runtime index) ∧
        type_of% (newest_input_energy runtime index) ∧ type_of% (finite_next_missing_cost runtime index)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCopyTimeGram.actual_recovery_consumed,
    fun runtime index => ⟨newest_observed runtime index, newest_time runtime index, boundary_coordinate runtime index,
      boundary_nonzero runtime index, newest_input_energy runtime index, finite_next_missing_cost runtime index⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyTimeGram.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyTimeGram.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyTemporalBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
