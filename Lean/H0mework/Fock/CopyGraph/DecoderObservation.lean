import H0mework.Fock.CopyGraph.DecoderField
import H0mework.Fock.CopyGraph.DecoderEffect
import H0mework.Fock.CopyGraph.ConditionalObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyObservation (twoMaterial before after joint)
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem original_after_recovery (value : FieldSpace 3 3) :
    fieldDecode 3 3 twoMaterial (after 3 3 twoMaterial)
      (SourceCopyGraph.action 3 twoMaterial (fieldRead 3 3 value)) = value := by
  change Actor.currentTransfer 3 3 (pullback (historyPMF 3) (after 3 3 twoMaterial)
    (decode 3 3 twoMaterial (after 3 3 twoMaterial)
      (SourceConditionalGraph.copyRead 3 3 twoMaterial (Actor.currentPullback 3 3 value)))) = value
  rw [after_decode_original]
  exact SourceCopyObservation.actual_original_recovery value

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    (∀ target : SourceJointClockGraph.Carrier,
      type_of% (original_minimum depth depth index (joint depth depth index) target) ∧
      type_of% (original_reconstruction depth depth index (joint depth depth index) target)) ∧
    (∀ value : FieldSpace depth depth,
      let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
      let remaining := value - fieldDecode depth depth index (joint depth depth index) target
      type_of% (conditional_gain depth depth index (joint depth depth index) (Actor.currentPullback depth depth value)) ∧
      type_of% (retained_lower depth depth index (joint depth depth index) (Actor.currentPullback depth depth value)) ∧
      type_of% (recovery_zero_iff depth depth index (joint depth depth index) (Actor.currentPullback depth depth value)) ∧
      type_of% (original_residual_energy depth depth index (joint depth depth index) value) ∧
      (∀ proposal : Space (observed (historyPMF depth) (joint depth depth index)),
        type_of% (normal_moments depth depth index (joint depth depth index) (Actor.currentPullback depth depth value) proposal)) ∧
      ∀ actor : Fin (depth + 1), type_of% (SourceGeneratedConditionalInventory.full_record_read runtime depth
        (Actor.currentPullback depth depth remaining) actor)) ∧
    SourceConditionalGraph.ObservationAt runtime index

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨(fun target => ⟨original_minimum _ _ index _ target, original_reconstruction _ _ index _ target⟩),
    (fun value => ⟨conditional_gain _ _ index _ (Actor.currentPullback _ _ value),
      retained_lower _ _ index _ (Actor.currentPullback _ _ value), recovery_zero_iff _ _ index _ (Actor.currentPullback _ _ value),
      original_residual_energy _ _ index _ value, normal_moments _ _ index _ (Actor.currentPullback _ _ value),
      SourceGeneratedConditionalInventory.full_record_read runtime _ _⟩),
    SourceConditionalGraph.observation_consumed runtime index⟩

def ActualRecovery : Prop :=
    type_of% old_conditional_not_decoder ∧ type_of% strict_clock_improvement ∧ type_of% before_minimum_positive ∧
      (∀ value : FieldSpace 3 3, type_of% (original_after_recovery value)) ∧
      type_of% (SourceCopyProgram.material_program 3 twoMaterial) ∧
      type_of% (SourceCopyProgram.copy_written_program 3 twoMaterial)

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨old_conditional_not_decoder, strict_clock_improvement, before_minimum_positive, original_after_recovery,
    SourceCopyProgram.material_program 3 twoMaterial, SourceCopyProgram.copy_written_program 3 twoMaterial⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceConditionalGraph.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt (roundRuntime round) index ∧
        ∀ value : FieldSpace depth depth,
          let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
          type_of% (original_residual_realization round depth depth index (before depth depth) value) ∧
          type_of% (original_residual_realization round depth depth index (joint depth depth index) value) ∧
          SourceCopyGraph.FieldAt round depth depth index
            (value - fieldDecode depth depth index (before depth depth) target) ∧
          SourceCopyGraph.FieldAt round depth depth index
            (value - fieldDecode depth depth index (joint depth depth index) target)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  exact ⟨SourceConditionalGraph.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun value => ⟨original_residual_realization round _ _ index _ value,
        original_residual_realization round _ _ index _ value,
        SourceCopyGraph.original_field_consumed round _ _ index _,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
