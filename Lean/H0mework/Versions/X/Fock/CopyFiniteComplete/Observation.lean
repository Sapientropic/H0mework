import H0mework.Versions.X.Fock.CopyFiniteComplete.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourcePrimeHistoryRecovery
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2 windowMeasurable

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    SourceCompleteGraph.ObservationAt runtime index ∧ SourceGraphRefinement.PrefixAt runtime index ∧
      type_of% (completed_history_target runtime) ∧ type_of% (next_history_target runtime) ∧
      type_of% (normal_inventory runtime) ∧ type_of% (last_cell_is_normal runtime) ∧
      (∀ actor : Fin (depth + 1), ∀ time : Fin (windowBound sourceOwner depth + 1),
        type_of% (completed_cell runtime actor time) ∧ type_of% (completed_material_factorizes runtime actor time) ∧
          type_of% (next_material_factorizes runtime actor time)) ∧
      type_of% (recovery_model depth runtime index) ∧ type_of% (recovery_next runtime index) ∧
      (∀ target : SourceJointClockGraph.Carrier, type_of% (residual_model depth runtime index target) ∧
        type_of% (reconstruction runtime index target) ∧ type_of% (recovery_full_record runtime index target)) ∧
      type_of% (recorded_boundary_nonzero runtime index) ∧
      type_of% ((normal runtime).target_factorizes) ∧
      type_of% (coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCompleteGraph.observation_consumed runtime index, SourceGraphRefinement.prefix_consumed runtime index,
    completed_history_target runtime, next_history_target runtime, normal_inventory runtime, last_cell_is_normal runtime,
    fun actor time => ⟨completed_cell runtime actor time, completed_material_factorizes runtime actor time,
      next_material_factorizes runtime actor time⟩,
    recovery_model _ runtime index, recovery_next runtime index,
    fun target => ⟨residual_model _ runtime index target, reconstruction runtime index target, recovery_full_record runtime index target⟩,
    recorded_boundary_nonzero runtime index, (normal runtime).target_factorizes,
    coversAt_factorizes (normal runtime).targetRuntime.tick.next .particleWave⟩

def ActualRecovery : Prop :=
    SourceCompleteGraph.ActualRecovery ∧ type_of% SourceFixedInventoryRecovery.actual_recovery_consumed ∧
      type_of% (recovery_model 2 (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2)) )) ∧
      type_of% (recorded_boundary_nonzero (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))))

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCompleteGraph.actual_recovery_consumed, SourceFixedInventoryRecovery.actual_recovery_consumed,
    recovery_model 2 (runtimeAt 2) 0, recorded_boundary_nonzero (runtimeAt 2) 0⟩

def RoundAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let depth := sourceDepth round
    SourceCompleteGraph.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt runtime index ∧
        (∀ target : SourceJointClockGraph.Carrier,
          type_of% (recovery_realization round runtime index target) ∧
            SourceCopyGraph.FieldAt round depth depth index (recovery runtime index target)) ∧
        ∀ value : FieldSpace depth depth,
          let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
          type_of% (field_recovery runtime index value) ∧ type_of% (original_energy runtime index value) ∧
            type_of% (residual_realization round runtime index value) ∧
            SourceCopyGraph.FieldAt round depth depth index (value - recovery runtime index target)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceCompleteGraph.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun target => ⟨recovery_realization round (roundRuntime round) index target,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩,
      fun value => ⟨field_recovery (roundRuntime round) index value, original_energy (roundRuntime round) index value,
        residual_realization round (roundRuntime round) index value, SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
