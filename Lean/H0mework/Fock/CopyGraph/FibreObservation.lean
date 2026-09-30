import H0mework.Fock.CopyGraph.FibreNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphFibreUpdate

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceOwnedObservationHistory
open SourceCopyProgram (Index sourceDepth)
open SourceGraphGrowth (sourceRead oldRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationFibreMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    let read := sourceRead depth index
    SourceGraphLoss.ObservationAt runtime index ∧ type_of% (source_update_is_loss depth index read) ∧
      type_of% (field_recovery_linear depth index read) ∧
      (∀ value : SourceJointClockGraph.Carrier, type_of% (prediction_source depth index read value) ∧
        type_of% (field_recovery_source depth index read value)) ∧
      (∀ supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support,
        type_of% (normal_fresh_pairing depth index read supported) ∧ type_of% (normal_ne_zero depth index read supported) ∧
        type_of% (direction_formula depth index read supported) ∧ type_of% (direction_cost depth index read supported) ∧
        ∀ actor : Fin (depth + 2), type_of% (SourceGraphGrowth.native_record_read (depth + 1)
          (Actor.currentPullback (depth + 1) (depth + 1) (normalField depth index read supported)) actor)) ∧
      type_of% (source_normal_account runtime index) ∧ type_of% (source_next_account runtime index)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceGraphLoss.observation_consumed runtime index, source_update_is_loss _ index _,
    field_recovery_linear _ index _, (fun value => ⟨prediction_source _ index _ value, field_recovery_source _ index _ value⟩),
    (fun supported => ⟨normal_fresh_pairing _ index _ supported, normal_ne_zero _ index _ supported,
      direction_formula _ index _ supported, direction_cost _ index _ supported, SourceGraphGrowth.native_record_read _ _⟩),
    source_normal_account runtime index, source_next_account runtime index⟩

def ActualRecovery : Prop :=
    SourceGraphLoss.ActualRecovery ∧ type_of% native_prior_supported ∧ type_of% native_normal_nonzero ∧ type_of% native_novel_zero

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨SourceGraphLoss.actual_recovery_consumed, native_prior_supported, native_normal_nonzero, native_novel_zero⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceGraphLoss.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth,
        let read := sourceRead depth index
        let freshIndex := FamilyModel.Fock.oldIndex depth index
        ObservationAt (roundRuntime round) index ∧
          ∀ supported : read (depth + 1) ∈ (observed (historyPMF depth) (oldRead depth read)).support,
            SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex (normalField depth index read supported) ∧
            ∀ value : SourceJointClockGraph.Carrier,
              type_of% (original_update_realization round depth index read supported value) ∧
              SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex
                ((inner ℂ (normal depth index read supported) value / ((‖normal depth index read supported‖ ^ 2 : ℝ) : ℂ)) • normalField depth index read supported)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceGraphLoss.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun supported => ⟨SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _,
        fun value => ⟨original_update_realization round _ index _ supported value,
          SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _⟩⟩⟩⟩

end
end SourceGraphFibreUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
