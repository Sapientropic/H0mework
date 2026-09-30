import H0mework.Fock.CopyGraph.FutureUpdateEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureUpdate

open SourceCopyProgram (Index sourceDepth)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem material_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    type_of% (SourceGraphRecurrence.material_history_step runtime index (steps + 1)) ∧
      type_of% (update_model_source runtime index steps target) ∧ type_of% (dimension_gain runtime index steps) ∧
      type_of% (sample_count runtime index) ∧ type_of% (block_partition runtime index steps target) ∧
      type_of% (gain_source runtime index steps target) ∧ type_of% (gain_budget runtime index steps target) ∧
      type_of% (recovery_balance runtime index steps target) ∧
      type_of% (SourceCopyFutureCoordinates.history_budget runtime index (steps + 1) target) := by
  with_reducible exact ⟨SourceGraphRecurrence.material_history_step runtime index (steps + 1),
    update_model_source runtime index steps target, dimension_gain runtime index steps, sample_count runtime index,
    block_partition runtime index steps target, gain_source runtime index steps target, gain_budget runtime index steps target,
    recovery_balance runtime index steps target, SourceCopyFutureCoordinates.history_budget runtime index (steps + 1) target⟩

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyFutureCoordinates.normal_consumed runtime index) ∧
      type_of% (material_consumed runtime index (frontier runtime).stageCount
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (normal runtime).targetRuntime)))) ∧
      type_of% (material_consumed runtime index ((frontier runtime).stageCount + 1)
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (normal runtime).targetRuntime.tick.next)))) ∧
      ∀ phase : Fin (index.val + 1),
        type_of% (native_query runtime index (frontier runtime).stageCount ((frontier runtime).stageCount + 1) phase) ∧
        type_of% (native_query runtime index ((frontier runtime).stageCount + 1) ((frontier runtime).stageCount + 2) phase) := by
  with_reducible exact ⟨SourceCopyFutureCoordinates.normal_consumed runtime index,
    material_consumed runtime index _ _, material_consumed runtime index _ _,
    fun phase => ⟨native_query runtime index _ _ phase, native_query runtime index _ _ phase⟩⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyFutureCoordinates.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      ∀ steps : Nat, (∀ target : SourceJointClockGraph.Carrier, type_of% (material_consumed runtime index steps target) ∧
        type_of% (update_source runtime index steps target)) ∧
        type_of% (no_free_update runtime index steps) ∧ type_of% (block_nonzero runtime index steps) ∧
        type_of% (tail_strict runtime index steps) ∧
        ∀ ticks : Nat, ∀ phase : Fin (index.val + 1), type_of% (native_query runtime index steps ticks phase)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCopyFutureCoordinates.observation_consumed runtime index, normal_consumed runtime index,
    fun steps => ⟨fun target => ⟨material_consumed runtime index steps target, update_source runtime index steps target⟩,
      no_free_update runtime index steps, block_nonzero runtime index steps, tail_strict runtime index steps,
      native_query runtime index steps⟩⟩

def ActualRecovery : Prop :=
    SourceCopyFutureCoordinates.ActualRecovery ∧
      ∀ runtime : LivingRuntimeState process, ∀ index : Index (inventoryBound runtime), ∀ steps : Nat,
        type_of% (dimension_gain runtime index steps) ∧ type_of% (block_nonzero runtime index steps) ∧
        type_of% (tail_strict runtime index steps) ∧ type_of% (no_free_update runtime index steps)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCopyFutureCoordinates.actual_recovery_consumed,
    fun runtime index steps => ⟨dimension_gain runtime index steps, block_nonzero runtime index steps,
      tail_strict runtime index steps, no_free_update runtime index steps⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyFutureCoordinates.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyFutureCoordinates.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyFutureUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
