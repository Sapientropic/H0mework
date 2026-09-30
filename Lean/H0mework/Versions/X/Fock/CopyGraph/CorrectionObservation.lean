import H0mework.Versions.X.Fock.CopyGraph.CorrectionField
import H0mework.Versions.X.Fock.CopyGraph.CorrectionEffect
import H0mework.Versions.X.Fock.CopyGraph.DecoderObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyObservation (before after joint twoMaterial)
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem actual_after_recovery (value : FieldSpace 3 3) : fieldRecovery 3 3 twoMaterial (after 3 3 twoMaterial) value = value := by
  rw [field_recovery_original]
  exact SourceConditionalGraphDecoder.original_after_recovery value

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    type_of% (denominator_pos depth depth index (joint depth depth index)) ∧
      type_of% (recovery_linear depth depth index (joint depth depth index)) ∧
      (∀ value : FieldSpace depth depth,
        type_of% (field_recovery_original depth depth index (joint depth depth index) value) ∧
        type_of% (original_minimum depth depth index (joint depth depth index) value) ∧
        type_of% (decoded_residual_mass depth depth index (joint depth depth index) (Actor.currentPullback depth depth value)) ∧
        ∀ actor : Fin (depth + 1), type_of% (SourceGeneratedConditionalInventory.full_record_read runtime depth
          (Actor.currentPullback depth depth (value - fieldRecovery depth depth index (joint depth depth index) value)) actor)) ∧
      (∀ atom : ParentCarrier × ParentCarrier,
        ∀ supported : atom ∈ (observed (historyPMF depth) (joint depth depth index)).support,
          type_of% (clock_mean_conditional depth (joint depth depth index) atom supported)) ∧
      SourceConditionalGraphDecoder.ObservationAt runtime index

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨denominator_pos _ _ index _, recovery_linear _ _ index _,
    (fun value => ⟨field_recovery_original _ _ index _ value, original_minimum _ _ index _ value,
      decoded_residual_mass _ _ index _ (Actor.currentPullback _ _ value),
      SourceGeneratedConditionalInventory.full_record_read runtime _ _⟩),
    clock_mean_conditional _ _, SourceConditionalGraphDecoder.observation_consumed runtime index⟩

def ActualRecovery : Prop :=
    type_of% before_pair_ne_zero ∧ type_of% before_coefficient_ne_zero ∧ type_of% before_optimal_mass_ne_zero ∧
      type_of% before_update_ne_zero ∧ (∀ value : FieldSpace 3 3, type_of% (actual_after_recovery value)) ∧
      SourceConditionalGraphDecoder.ActualRecovery

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨before_pair_ne_zero, before_coefficient_ne_zero, before_optimal_mass_ne_zero, before_update_ne_zero,
    actual_after_recovery, SourceConditionalGraphDecoder.actual_recovery_consumed⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceConditionalGraphDecoder.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt (roundRuntime round) index ∧
        ∀ value : FieldSpace depth depth,
          type_of% (original_residual_realization round depth depth index (before depth depth) value) ∧
          type_of% (original_residual_realization round depth depth index (joint depth depth index) value) ∧
          SourceCopyGraph.FieldAt round depth depth index (value - fieldRecovery depth depth index (before depth depth) value) ∧
          SourceCopyGraph.FieldAt round depth depth index (value - fieldRecovery depth depth index (joint depth depth index) value)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  exact ⟨SourceConditionalGraphDecoder.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun value => ⟨original_residual_realization round _ _ index _ value,
        original_residual_realization round _ _ index _ value,
        SourceCopyGraph.original_field_consumed round _ _ index _,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
