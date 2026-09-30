import H0mework.Versions.X.Fock.CopyGraph.FutureCoordinatesAccount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index sourceDepth)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem material_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    type_of% (SourceGraphRecurrence.material_history_step runtime index steps) ∧
      type_of% (model_equiv_source runtime index steps target) ∧ type_of% (model_dimension runtime index steps) ∧
      type_of% (window_reconstruction runtime index steps target) ∧ type_of% (window_energy runtime index steps target) ∧
      type_of% (original_residual_partition runtime index steps target) ∧ type_of% (history_budget runtime index steps target) ∧
      type_of% (residual_next runtime index steps target) := by
  with_reducible exact ⟨SourceGraphRecurrence.material_history_step runtime index steps,
    model_equiv_source runtime index steps target, model_dimension runtime index steps,
    window_reconstruction runtime index steps target, window_energy runtime index steps target,
    original_residual_partition runtime index steps target, history_budget runtime index steps target,
    residual_next runtime index steps target⟩

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyFutureAcquisition.normal_consumed runtime index) ∧
      type_of% (material_consumed runtime index (frontier runtime).stageCount
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (normal runtime).targetRuntime)))) ∧
      type_of% (material_consumed runtime index ((frontier runtime).stageCount + 1)
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (normal runtime).targetRuntime.tick.next)))) ∧
      type_of% (native_step runtime index (frontier runtime).stageCount ((frontier runtime).stageCount + 1)) ∧
      type_of% (native_step runtime index ((frontier runtime).stageCount + 1) ((frontier runtime).stageCount + 2)) := by
  with_reducible exact ⟨SourceCopyFutureAcquisition.normal_consumed runtime index,
    material_consumed runtime index _ _, material_consumed runtime index _ _,
    native_step runtime index _ _, native_step runtime index _ _⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyFutureAcquisition.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      ∀ steps : Nat, type_of% (kernel_exact runtime index steps) ∧ type_of% (model_dimension runtime index steps) ∧
        (∀ left right : SourceJointClockGraph.Carrier, type_of% (model_coordinates runtime index steps left right) ∧
          type_of% (complete_fibre runtime index steps left right) ∧ type_of% (material_consumed runtime index steps left)) ∧
        (∀ value : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)),
          type_of% (model_step runtime index steps value)) ∧
        type_of% (hidden_retained runtime index steps) ∧ type_of% (hidden_residual runtime index steps) ∧
        ∀ ticks : Nat, type_of% (native_step runtime index steps ticks)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCopyFutureAcquisition.observation_consumed runtime index, normal_consumed runtime index,
    fun steps => ⟨kernel_exact runtime index steps, model_dimension runtime index steps,
      fun left right => ⟨model_coordinates runtime index steps left right, complete_fibre runtime index steps left right,
        material_consumed runtime index steps left⟩,
      model_step runtime index steps, hidden_retained runtime index steps, hidden_residual runtime index steps,
      native_step runtime index steps⟩⟩

def ActualRecovery : Prop :=
    SourceCopyFutureAcquisition.ActualRecovery ∧
      ∀ runtime : LivingRuntimeState process, ∀ index : Index (inventoryBound runtime), ∀ steps : Nat,
        type_of% (SourceCopyRecordedRecurrence.hidden_nonzero runtime index (steps + 1)) ∧
        type_of% (hidden_retained runtime index steps) ∧ type_of% (hidden_residual runtime index steps) ∧
        ∀ target : SourceJointClockGraph.Carrier, type_of% (window_energy runtime index steps target) ∧
          type_of% (history_budget runtime index steps target)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCopyFutureAcquisition.actual_recovery_consumed,
    fun runtime index steps => ⟨SourceCopyRecordedRecurrence.hidden_nonzero runtime index (steps + 1),
      hidden_retained runtime index steps, hidden_residual runtime index steps,
      fun target => ⟨window_energy runtime index steps target, history_budget runtime index steps target⟩⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyFutureAcquisition.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyFutureAcquisition.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
