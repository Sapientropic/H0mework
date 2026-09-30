import H0mework.Versions.X.Fock.CopyGraph.LossTrace

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceOwnedObservationHistory
open SourceCopyProgram (Index sourceDepth)
open SourceGraphGrowth (sourceRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationLossMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    let read := sourceRead depth index
    SourceGraphBirth.ObservationAt runtime index ∧ type_of% (update_is_loss depth index read) ∧
      type_of% (direction_zero_iff_novel depth index read) ∧ type_of% (native_rank_increment depth index) ∧
      (∀ value : SourceJointClockGraph.Carrier, type_of% (whole_field_update depth index read value) ∧
        type_of% (prediction_source depth index read value) ∧ type_of% (complete_budget depth index read value) ∧
        type_of% (loss_zero_iff depth index read value)) ∧
      (∀ prime : Nat.Prime (2 * depth + 5), type_of% (native_prime_update_zero depth index prime)) ∧
      (∀ step : Nat, type_of% (step_rank_increment runtime index step)) ∧
      type_of% (normal_rank_cost runtime index) ∧ type_of% (generated_next_rank_cost runtime index) ∧
      ∀ actor : Fin (depth + 2), type_of% (SourceGraphGrowth.native_record_read (depth + 1)
        (Actor.currentPullback (depth + 1) (depth + 1) (directionField depth index read)) actor)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceGraphBirth.observation_consumed runtime index, update_is_loss _ index _,
    direction_zero_iff_novel _ index _, native_rank_increment _ index,
    (fun value => ⟨whole_field_update _ index _ value, prediction_source _ index _ value,
      complete_budget _ index _ value, loss_zero_iff _ index _ value⟩), native_prime_update_zero _ index,
    step_rank_increment runtime index, normal_rank_cost runtime index, generated_next_rank_cost runtime index,
    SourceGraphGrowth.native_record_read _ _⟩

def ActualRecovery : Prop :=
    SourceGraphBirth.ActualRecovery ∧ type_of% native_collision_cost ∧ type_of% native_pulse_pair_ne_zero ∧
      type_of% (native_prime_update_zero 0 (0 : Index 0) (by decide : Nat.Prime (2 * 0 + 5)))

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceGraphBirth.actual_recovery_consumed, native_collision_cost, native_pulse_pair_ne_zero,
    native_prime_update_zero 0 (0 : Index 0) (by decide)⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceGraphBirth.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth,
        let read := sourceRead depth index
        let freshIndex := FamilyModel.Fock.oldIndex depth index
        ObservationAt (roundRuntime round) index ∧
          SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex (directionField depth index read) ∧
          ∀ value : SourceJointClockGraph.Carrier,
            type_of% (original_loss_realization round depth index read value) ∧
            SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex
              ((inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • directionField depth index read)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceGraphBirth.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _,
      fun value => ⟨original_loss_realization round _ index _ value,
        SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _⟩⟩⟩

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
