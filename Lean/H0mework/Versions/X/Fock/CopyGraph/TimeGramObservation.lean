import H0mework.Versions.X.Fock.CopyGraph.TimeGramEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index sourceDepth)
open SourceCopyTimeModel (Packet phases modelStep finitePhases)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_model_next (depth : Nat) (index : Index depth) (runtime : LivingRuntimeState process) :
    modelStep depth index (model depth index (phases depth index (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point runtime))))) =
      model depth index (phases depth index (SourceJointClockGraph.read
        (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next)))) := by
  rw [model_source, model_source]
  exact SourceCopyTimeModel.model_native_next depth index runtime

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyTimeEnergy.normal_consumed runtime index) ∧
      type_of% (native_model_next (inventoryBound runtime) index (normal runtime).targetRuntime) ∧
      type_of% (native_model_next (inventoryBound runtime) index (normal runtime).targetRuntime.tick.next) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (finite_source_error runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (finite_old_comparison runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (finite_next_correction runtime index ((frontier runtime).stageCount + 1) target) ∧
        type_of% (finite_source_error runtime index ((frontier runtime).stageCount + 2) target) ∧
        type_of% (finite_old_comparison runtime index ((frontier runtime).stageCount + 2) target) ∧
        type_of% (finite_next_correction runtime index ((frontier runtime).stageCount + 2) target) :=
  ⟨SourceCopyTimeEnergy.normal_consumed runtime index, native_model_next _ index _, native_model_next _ index _,
    fun target => ⟨finite_source_error runtime index _ target, finite_old_comparison runtime index _ target,
      finite_next_correction runtime index _ target, finite_source_error runtime index _ target,
      finite_old_comparison runtime index _ target, finite_next_correction runtime index _ target⟩⟩

theorem packet_consumed (depth : Nat) (index : Index depth) (packet : Packet depth index) :
      type_of% (normal_equation depth index packet) ∧
        type_of% (residual_normal depth index packet) ∧ type_of% (model_next_correction depth index packet) ∧
        (∀ other : Packet depth index, type_of% (complete_fibre depth index packet other)) ∧
        ∀ proposal : SourceJointClockGraph.Carrier, type_of% (error_energy depth index packet proposal) ∧
          type_of% (minimum_fibre depth index packet proposal) := by
  refine ⟨normal_equation depth index packet, residual_normal depth index packet,
    model_next_correction depth index packet, ?_, ?_⟩
  · intro other
    exact complete_fibre depth index packet other
  · intro proposal
    exact ⟨error_energy depth index packet proposal, minimum_fibre depth index packet proposal⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    SourceCopyTimeEnergy.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      (∀ packet : Packet depth index, type_of% (packet_consumed depth index packet)) ∧
      (∀ target : SourceJointClockGraph.Carrier, type_of% (solve_equation depth index target) ∧
        type_of% (decode_source depth index target) ∧ type_of% (finite_tendsto runtime index target) ∧
        ∀ steps : Nat, type_of% (finite_source_error runtime index steps target) ∧
          type_of% (finite_old_comparison runtime index steps target) ∧
          type_of% (finite_next_correction runtime index steps target)) ∧
      type_of% (native_model_next depth index runtime)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  refine ⟨SourceCopyTimeEnergy.observation_consumed runtime index, normal_consumed runtime index, ?_, ?_,
    native_model_next (inventoryBound runtime) index runtime⟩
  · intro packet
    with_reducible exact packet_consumed (inventoryBound runtime) index packet
  · intro target
    with_reducible exact ⟨solve_equation (inventoryBound runtime) index target, decode_source (inventoryBound runtime) index target,
      finite_tendsto runtime index target, fun steps => ⟨finite_source_error runtime index steps target,
        finite_old_comparison runtime index steps target, finite_next_correction runtime index steps target⟩⟩

def ActualRecovery : Prop :=
    SourceCopyTimeEnergy.ActualRecovery ∧ type_of% two_index_source ∧ type_of% stale_source ∧
      type_of% stale_correction ∧ type_of% stale_feedback_nonzero

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceCopyTimeEnergy.actual_recovery_consumed, two_index_source, stale_source, stale_correction, stale_feedback_nonzero⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyTimeEnergy.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyTimeEnergy.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
