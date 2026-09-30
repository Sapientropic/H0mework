import H0mework.Versions.X.Fock.CopyGraph.RecordedRecurrenceEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecordedRecurrence

open SourceCopyProgram (Index sourceDepth)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyTemporalAcquisition.normal_consumed runtime index) ∧
      ∀ ticks : Nat,
        type_of% (native_future runtime index ((frontier runtime).stageCount + 1) ticks) ∧
        type_of% (native_future runtime index ((frontier runtime).stageCount + 2) ticks) := by
  with_reducible exact ⟨SourceCopyTemporalAcquisition.normal_consumed runtime index,
    fun ticks => ⟨native_future runtime index _ ticks, native_future runtime index _ ticks⟩⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyTemporalAcquisition.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      ∀ steps : Nat, type_of% (source_law runtime index steps) ∧ type_of% (advance_source runtime index steps) ∧
        (∀ target other : SourceJointClockGraph.Carrier, type_of% (full_future_fibre runtime index steps target other) ∧
          type_of% (model_fibre runtime index steps target other) ∧
          ∀ ticks : Nat, type_of% (read_future runtime index steps ticks target)) ∧
        type_of% (hidden_source runtime index steps) ∧ type_of% (hidden_nonzero runtime index steps) ∧
        (∀ ticks : Nat, type_of% (hidden_future_zero runtime index steps ticks)) ∧ type_of% (no_source_decoder runtime index steps)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCopyTemporalAcquisition.observation_consumed runtime index, normal_consumed runtime index,
    fun steps => ⟨source_law runtime index steps, advance_source runtime index steps,
      fun target other => ⟨full_future_fibre runtime index steps target other, model_fibre runtime index steps target other,
        fun ticks => read_future runtime index steps ticks target⟩,
      hidden_source runtime index steps, hidden_nonzero runtime index steps,
      hidden_future_zero runtime index steps, no_source_decoder runtime index steps⟩⟩

def ActualRecovery : Prop :=
    SourceCopyTemporalAcquisition.ActualRecovery ∧
      ∀ runtime : LivingRuntimeState process, ∀ index : Index (inventoryBound runtime), ∀ steps : Nat,
        type_of% (hidden_nonzero runtime index steps) ∧ type_of% (hidden_same_window runtime index steps) ∧
        ∀ ticks : Nat, type_of% (native_future runtime index steps ticks) ∧ type_of% (hidden_future_zero runtime index steps ticks)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCopyTemporalAcquisition.actual_recovery_consumed,
    fun runtime index steps => ⟨hidden_nonzero runtime index steps, hidden_same_window runtime index steps,
      fun ticks => ⟨native_future runtime index steps ticks, hidden_future_zero runtime index steps ticks⟩⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyTemporalAcquisition.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyTemporalAcquisition.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyRecordedRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
