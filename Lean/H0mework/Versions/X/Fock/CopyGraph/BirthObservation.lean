import H0mework.Versions.X.Fock.CopyGraph.BirthUpdate
import H0mework.Versions.X.Fock.CopyGraph.BirthRange

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceOwnedObservationHistory
open SourceCopyProgram (Index sourceDepth)
open SourceGraphGrowth (sourceRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationBirthMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    let read := sourceRead depth index
    SourceGraphGrowth.ObservationAt runtime index ∧
      type_of% (innovation_ne_zero depth index read) ∧ type_of% (update_is_birth depth index read) ∧
      type_of% (birth_range depth index read) ∧ type_of% (birth_finrank depth index read) ∧
      (∀ value : SourceJointClockGraph.Carrier, type_of% (birth_formula depth index read value) ∧
        type_of% (field_decoder_update depth index read value) ∧ type_of% (growth_update_cost depth index read value) ∧
        type_of% (birth_zero_iff depth index read value)) ∧
      type_of% (fresh_field_recovery depth index read) ∧ type_of% (fresh_gain_positive depth index read) ∧
      (∀ actor : Fin (depth + 2),
        type_of% (SourceGraphGrowth.native_record_read (depth + 1)
          (Actor.currentPullback (depth + 1) (depth + 1) (innovationField depth index read)) actor) ∧
        type_of% (SourceGraphGrowth.native_record_read (depth + 1)
          (Actor.currentPullback (depth + 1) (depth + 1) (freshField depth)) actor))

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨SourceGraphGrowth.observation_consumed runtime index,
    innovation_ne_zero _ index _, update_is_birth _ index _, birth_range _ index _, birth_finrank _ index _,
    (fun value => ⟨birth_formula _ index _ value, field_decoder_update _ index _ value,
      growth_update_cost _ index _ value, birth_zero_iff _ index _ value⟩),
    fresh_field_recovery _ index _, fresh_gain_positive _ index _,
    fun actor => ⟨SourceGraphGrowth.native_record_read _ _ actor, SourceGraphGrowth.native_record_read _ _ actor⟩⟩

def ActualRecovery : Prop :=
    SourceGraphGrowth.ActualRecovery ∧
      type_of% (fresh_gain_positive 2 (0 : Index 2) (sourceRead 2 (0 : Index 2))) ∧
      type_of% (fresh_field_recovery 2 (0 : Index 2) (sourceRead 2 (0 : Index 2))) ∧
      type_of% (birth_finrank 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)))

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨SourceGraphGrowth.actual_recovery_consumed, fresh_gain_positive 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)),
    fresh_field_recovery 2 (0 : Index 2) (sourceRead 2 (0 : Index 2)), birth_finrank 2 (0 : Index 2) (sourceRead 2 (0 : Index 2))⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceGraphGrowth.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth,
        let read := sourceRead depth index
        let freshIndex := FamilyModel.Fock.oldIndex depth index
        ObservationAt (roundRuntime round) index ∧
          SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex (freshField depth) ∧
          SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex (innovationField depth index read) ∧
          ∀ value : SourceJointClockGraph.Carrier,
            type_of% (original_birth_realization round depth index read value) ∧
            SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex
              ((inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovationField depth index read)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceGraphGrowth.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _,
      SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _,
      fun value => ⟨original_birth_realization round _ index _ value,
        SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _⟩⟩⟩

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
