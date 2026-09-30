import H0mework.Versions.X.Fock.CopyGraph.ColumnForcingRecorded

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceColumnForcing

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceFiniteCompleteGraph.windowMeasurable

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    let query := SourceFiniteCompleteGraph.completedRecord runtime
    SourceNormalInverse.ObservationAt runtime index ∧ type_of% (no_free_target runtime index) ∧
      (∀ value : FieldSpace depth depth, type_of% (actual_field_recovery runtime index value)) ∧
      ∀ target : SourceJointClockGraph.Carrier,
        type_of% (forcing_source depth depth index query target) ∧
        type_of% (recovery_source runtime index target) ∧ type_of% (recovery_next runtime index target) ∧
        type_of% (decode_equation depth depth index query target) ∧
        (∀ other : SourceJointClockGraph.Carrier, type_of% (complete_fibre depth depth index query target other)) ∧
        ∀ atom supported, type_of% (forcing_conditional depth depth index query target atom supported)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceNormalInverse.observation_consumed runtime index, no_free_target runtime index,
    actual_field_recovery runtime index, fun target => ⟨forcing_source _ _ index _ target,
      recovery_source runtime index target, recovery_next runtime index target, decode_equation _ _ index _ target,
      complete_fibre _ _ index _ target, forcing_conditional _ _ index _ target⟩⟩

def ActualRecovery : Prop :=
    SourceNormalInverse.ActualRecovery ∧ type_of% (no_free_target (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))))

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceNormalInverse.actual_recovery_consumed, no_free_target (runtimeAt 2) 0⟩

def RoundAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let depth := sourceDepth round
    SourceNormalInverse.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt runtime index ∧
        ∀ target : SourceJointClockGraph.Carrier,
          type_of% (recovery_realization round runtime index target) ∧
            SourceCopyGraph.FieldAt round depth depth index (recovery runtime index target)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceNormalInverse.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun target => ⟨recovery_realization round _ index target,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceColumnForcing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
