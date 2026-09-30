import H0mework.Fock.CopyGraph.GrowthEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedAcquisitionJoint (normalize)
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceOwnedObservationHistory
open SourceCopyProgram (Index sourceDepth)
open SourceConditionalGraphDecoder (fieldDecode)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationGrowthMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    let read := sourceRead depth index
    type_of% (old_material depth index) ∧ type_of% (source_read_written depth index) ∧
      type_of% (old_read_joint depth index) ∧ type_of% (new_read_joint depth index) ∧
      type_of% (tagged_old_distribution depth read) ∧
      (∀ atom, ∀ supported : atom ∈ (SourceConditionalHistory.observed
          (SourceConditionalHistory.observed (historyPMF (depth + 1)) (taggedRead depth read)) Prod.fst).support,
        type_of% (forgetting_conditional depth read atom supported)) ∧
      (∀ value : SourceJointClockGraph.Carrier, type_of% (growth_residual depth index read value) ∧
        type_of% (growth_energy depth index read value) ∧ type_of% (no_free_monotonicity depth index read value)) ∧
      (∀ value : Space (observed (historyPMF depth) (oldRead depth read)),
        type_of% (tagged_field_recovery depth index read value)) ∧
      (∀ value : FieldSpace depth depth,
        let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
        let remaining := normalize depth (depth + 1) (Nat.le_succ depth) value -
          fieldDecode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) target
        type_of% (original_growth_budget depth index read value) ∧
        ∀ actor : Fin (depth + 2),
          type_of% (native_record_read (depth + 1)
            (Actor.currentPullback (depth + 1) (depth + 1) (birthField depth index read target)) actor) ∧
          type_of% (native_record_read (depth + 1)
            (Actor.currentPullback (depth + 1) (depth + 1) (forgettingField depth index read target)) actor) ∧
          type_of% (native_record_read (depth + 1)
            (Actor.currentPullback (depth + 1) (depth + 1) remaining) actor)) ∧
      SourceGraphRefinement.ObservationAt runtime index

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨old_material _ index, source_read_written _ index, old_read_joint _ index, new_read_joint _ index,
    tagged_old_distribution _ _, forgetting_conditional _ _,
    (fun value => ⟨growth_residual _ index _ value, growth_energy _ index _ value, no_free_monotonicity _ index _ value⟩),
    tagged_field_recovery _ index _,
    (fun value => ⟨original_growth_budget _ index _ value,
      fun actor => ⟨native_record_read _ _ actor, native_record_read _ _ actor, native_record_read _ _ actor⟩⟩),
    SourceGraphRefinement.observation_consumed runtime index⟩

def ActualRecovery : Prop :=
    type_of% native_unit_collision ∧ type_of% (native_old_recovery 2 (0 : Index 2)) ∧
      type_of% (native_tagged_recovery 2 (0 : Index 2)) ∧ type_of% (native_tagged_field 2 (0 : Index 2)) ∧
      type_of% native_forgotten_cost ∧ type_of% native_forgetting_positive ∧ type_of% native_original_cost ∧
      SourceGraphRefinement.ActualRecovery

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨native_unit_collision, native_old_recovery 2 (0 : Index 2), native_tagged_recovery 2 (0 : Index 2),
    native_tagged_field 2 (0 : Index 2), native_forgotten_cost, native_forgetting_positive, native_original_cost,
    SourceGraphRefinement.actual_recovery_consumed⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceGraphRefinement.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt (roundRuntime round) index ∧
        ∀ value : FieldSpace depth depth,
          let read := sourceRead depth index
          let freshIndex := FamilyModel.Fock.oldIndex depth index
          let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
          type_of% (birth_realization round depth index read target) ∧
          type_of% (forgetting_realization round depth index read target) ∧
          SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex (birthField depth index read target) ∧
          SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex (forgettingField depth index read target) ∧
          SourceCopyGraph.FieldAt round (depth + 1) (depth + 1) freshIndex
            (normalize depth (depth + 1) (Nat.le_succ depth) value - fieldDecode (depth + 1) (depth + 1) freshIndex (newRead depth read) target) ∧
          SourceCopyGraph.FieldAt round depth depth index (value - fieldDecode depth depth index (oldRead depth read) target)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  with_reducible exact ⟨SourceGraphRefinement.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun _ => ⟨birth_realization round _ index _ _, forgetting_realization round _ index _ _,
        SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _,
        SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _,
        SourceCopyGraph.original_field_consumed round _ _ (FamilyModel.Fock.oldIndex _ index) _,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
