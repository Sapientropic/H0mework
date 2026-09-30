import H0mework.Versions.X.Fock.CopyGraph.FutureAcquisitionConditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureAcquisition

open SourceCopyProgram (Index sourceDepth)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionWords.Fock.Dynamic
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2

theorem material_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    type_of% (SourceGraphRecurrence.material_history_step runtime index steps) ∧
      type_of% (future_kernel_strict runtime index steps) ∧ type_of% (model_gain runtime index steps) ∧
      type_of% (recovered_birth runtime index steps) ∧ type_of% (acquired_error_strict runtime index steps) ∧
      type_of% (recovered_birth_budget runtime index steps) ∧
      type_of% (SourceRecordedEvolution.history_energy runtime index (steps + 1) (arrival runtime index steps)) := by
  with_reducible exact ⟨SourceGraphRecurrence.material_history_step runtime index steps,
    future_kernel_strict runtime index steps, model_gain runtime index steps, recovered_birth runtime index steps,
    acquired_error_strict runtime index steps, recovered_birth_budget runtime index steps,
    SourceRecordedEvolution.history_energy runtime index (steps + 1) _⟩

theorem normal_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% (SourceCopyRecordedRecurrence.normal_consumed runtime index) ∧
      type_of% (material_consumed runtime index ((frontier runtime).stageCount + 1)) ∧
      type_of% (material_consumed runtime index ((frontier runtime).stageCount + 2)) := by
  with_reducible exact ⟨SourceCopyRecordedRecurrence.normal_consumed runtime index,
    material_consumed runtime index _, material_consumed runtime index _⟩

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    SourceCopyRecordedRecurrence.ObservationAt runtime index ∧ type_of% (normal_consumed runtime index) ∧
      ∀ steps : Nat, type_of% (material_consumed runtime index steps) ∧ type_of% (acquired_read_nonzero runtime index steps) ∧
        type_of% (no_free_acquired_read runtime index steps) ∧
        (∀ actor : Fin (inventoryBound runtime + steps + 1 + 1), type_of% (acquired_samples runtime index steps actor)) ∧
        type_of% (acquired_forcing runtime index steps (Hilbert.read 0 (inventoryBound runtime + steps + 1))) ∧
        ∀ atom, ∀ supported : atom ∈ (observed (historyPMF (inventoryBound runtime + steps + 1))
          (Hilbert.read 0 (inventoryBound runtime + steps + 1))).support,
          type_of% (acquired_conditional runtime index steps (Hilbert.read 0 (inventoryBound runtime + steps + 1)) atom supported)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceCopyRecordedRecurrence.observation_consumed runtime index, normal_consumed runtime index,
    fun steps => ⟨material_consumed runtime index steps, acquired_read_nonzero runtime index steps,
      no_free_acquired_read runtime index steps, acquired_samples runtime index steps,
      acquired_forcing runtime index steps _, acquired_conditional runtime index steps _⟩⟩

def ActualRecovery : Prop :=
    SourceCopyRecordedRecurrence.ActualRecovery ∧
      ∀ runtime : LivingRuntimeState process, ∀ index : Index (inventoryBound runtime), ∀ steps : Nat,
        type_of% (acquired_pairing runtime index steps) ∧ type_of% (future_kernel_strict runtime index steps) ∧
        type_of% (acquired_error_strict runtime index steps) ∧ type_of% (model_gain runtime index steps)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceCopyRecordedRecurrence.actual_recovery_consumed,
    fun runtime index steps => ⟨acquired_pairing runtime index steps, future_kernel_strict runtime index steps,
      acquired_error_strict runtime index steps, model_gain runtime index steps⟩⟩

def RoundAt (round : Nat) : Prop :=
    SourceCopyRecordedRecurrence.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index (sourceDepth round), ObservationAt (roundRuntime round) index

theorem round_consumed (round : Nat) : RoundAt round :=
  ⟨SourceCopyRecordedRecurrence.round_consumed round, actual_recovery_consumed, observation_consumed (roundRuntime round)⟩

end
end SourceCopyFutureAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
