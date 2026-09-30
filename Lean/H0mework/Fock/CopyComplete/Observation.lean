import H0mework.Fock.CopyComplete.Trace

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceOwnedObservationHistory
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] completeUniform completeMeasurable completeBorel completeT2

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    SourceGraphRecurrence.ObservationAt runtime index ∧
      (∀ task : Fin (depth + 2) → ℂ, type_of% (Hilbert.dynamic_information_consumed depth task)) ∧
      type_of% (no_forgetting depth depth index) ∧ type_of% (normal_consumed depth runtime index) ∧
      ∀ steps : Nat, type_of% (recovery_canonical depth runtime index steps) ∧
        type_of% (history_boundary_nonzero depth runtime index steps) ∧
        (∀ value : SourceJointClockGraph.Carrier, type_of% (history_energy depth runtime index steps value) ∧
          ∀ actor : Fin (depth + steps + 1), type_of% (SourceGraphGrowth.native_record_read (depth + steps)
            (SourceGeneratedActionWords.Fock.OriginalHilbert.Actor.currentPullback (depth + steps) (depth + steps)
              (recovery depth runtime index steps value)) actor)) ∧
        ∀ value : FieldSpace (depth + steps) (depth + steps), type_of% (history_field_recovery depth runtime index steps value)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceGraphRecurrence.observation_consumed runtime index,
    Hilbert.dynamic_information_consumed _, no_forgetting _ _ index, normal_consumed _ runtime index,
    fun steps => ⟨recovery_canonical _ runtime index steps, history_boundary_nonzero _ runtime index steps,
      fun value => ⟨history_energy _ runtime index steps value, SourceGraphGrowth.native_record_read _ _⟩,
      history_field_recovery _ runtime index steps⟩⟩

def ActualRecovery : Prop := SourceGraphRecurrence.ActualRecovery ∧ type_of% native_complete_recovery ∧
    type_of% SourceGraphRecurrence.native_collision ∧
    type_of% (history_boundary_nonzero 2 (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))) 1)

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceGraphRecurrence.actual_recovery_consumed, native_complete_recovery,
    SourceGraphRecurrence.native_collision, history_boundary_nonzero 2 (runtimeAt 2) 0 1⟩

def RoundAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let depth := sourceDepth round
    SourceGraphRecurrence.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt runtime index ∧
        ∀ steps : Nat,
          let retained := SourceGraphLoss.advancedIndex depth index steps
          (∀ target : SourceJointClockGraph.Carrier,
            SourceCopyGraph.FieldAt round (depth + steps) (depth + steps) retained (recovery depth runtime index steps target)) ∧
          ∀ value : FieldSpace (depth + steps) (depth + steps),
            type_of% (field_realization round depth (depth + steps) (depth + steps) retained value) ∧
              SourceCopyGraph.FieldAt round (depth + steps) (depth + steps) retained value

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceGraphRecurrence.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun steps => ⟨fun _target => SourceCopyGraph.original_field_consumed round _ _ _ _,
        fun value => ⟨field_realization round _ _ _ _ value,
          SourceCopyGraph.original_field_consumed round _ _ _ _⟩⟩⟩⟩

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
