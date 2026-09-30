import H0mework.Versions.X.Fock.CopyGraph.NormalInverseRecorded

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNormalInverse

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceFiniteCompleteGraph.windowMeasurable

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    let query := SourceFiniteCompleteGraph.completedRecord runtime
    SourceFiniteCompleteGraph.ObservationAt runtime index ∧ type_of% (recovery_source runtime index) ∧
      type_of% (recovery_next runtime index) ∧
      (∀ forcing : SourceWeightedRecovery.Space (SourceWeightedRecovery.observed
          (SourceGeneratedRuntimeHistoryProbability.historyPMF depth) query),
        type_of% (solve_equation depth depth index query forcing)) ∧
      (∀ target : SourceJointClockGraph.Carrier, type_of% (recorded_equation runtime index target) ∧
        type_of% (remaining_source runtime index target) ∧ type_of% (source_minimum depth depth index query target)) ∧
      type_of% (boundary_nonzero runtime index)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceFiniteCompleteGraph.observation_consumed runtime index,
    recovery_source runtime index, recovery_next runtime index, solve_equation _ _ index _,
    fun target => ⟨recorded_equation runtime index target, remaining_source runtime index target,
      source_minimum _ _ index _ target⟩, boundary_nonzero runtime index⟩

def ActualRecovery : Prop :=
    SourceFiniteCompleteGraph.ActualRecovery ∧ type_of% (boundary_nonzero (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2)))) ∧
      type_of% (recovery_source (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))))

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceFiniteCompleteGraph.actual_recovery_consumed, boundary_nonzero (runtimeAt 2) 0, recovery_source (runtimeAt 2) 0⟩

def RoundAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let depth := sourceDepth round
    SourceFiniteCompleteGraph.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt runtime index ∧
        ∀ target : SourceJointClockGraph.Carrier,
          type_of% (source_realization round depth depth index (SourceFiniteCompleteGraph.completedRecord runtime) target) ∧
            SourceCopyGraph.FieldAt round depth depth index (recovery runtime index target)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceFiniteCompleteGraph.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun target => ⟨source_realization round _ _ index _ target,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceNormalInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
