import H0mework.Versions.X.Fock.HistoryModel.RecordedControls
import H0mework.Versions.X.Fock.HistoryModel.RecordedTransfer
import H0mework.Versions.X.Fock.PrimeFieldCalculation.CalculationConsumer
import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertConsumer

/-! Finite actual records generate the whole source update, both original transfers, the controlled normal and its canonical next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourcePrimeHistoryRecovery SourcePrimeCalculation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance recordedConsumerFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)

theorem recorded_word_calculation_consumed (bound : Nat) :
    let position := completionDepth sourceOwner bound + 1
    let depth := position + 1
    type_of% (source_payload_is_original bound) ∧
      (∀ stage : Fin ((frontier bound).stageCount + 1),
        (frontier bound).LocalOperationAt stage (frontier bound).sourcePayload ((frontier bound).history.stageAt stage)) ∧
      (∀ actor : Fin (bound + 1), type_of% (sourceWord_actual_birth bound actor) ∧
        type_of% (sourceWord_actual_point bound actor) ∧ type_of% (whole_recorded depth bound actor) ∧
        type_of% (recordedRestriction_nextRead depth bound actor) ∧ type_of% (sourceWord_recorded_ne_zero bound actor) ∧
        type_of% (recordedQuery_ne_zero bound actor) ∧ type_of% (recovered_actor_before_normal bound actor)) ∧
      type_of% (whole_pmf depth bound) ∧
      (∀ value : Field nativeStep (rawWords depth),
        ∀ supported : value ∈ (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound).support,
        type_of% (whole_on_actual_support depth bound value supported)) ∧
      (∀ actor : Fin (bound + 1), ∀ supported : Actor.nextRead depth bound actor ∈
          (SourceWeightedRecovery.observed (historyPMF bound) (Actor.nextRead depth bound)).support,
        type_of% (next_conditional_recorded depth bound actor supported)) ∧
      (∀ task : Fin (bound + 1) → ℂ, ∀ actor : Fin (bound + 1),
        type_of% (original_transfer_on_record depth bound task actor) ∧ type_of% (prime_transfer_on_record bound task actor)) ∧
      (∀ value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound,
        ∀ actor : Fin (bound + 1), type_of% (original_field_transfer_on_record depth bound value actor)) ∧
      type_of% (whole_at_acquisition_normal depth bound) ∧ type_of% (original_field_at_acquisition_normal depth bound) ∧
      type_of% (acquisition_stage_count bound) ∧ type_of% (last_record_is_target bound) ∧
      type_of% (last_record_is_generated_birth bound) ∧ type_of% (canonical_next_after_records bound) ∧
      type_of% (normal bound).target_factorizes ∧ type_of% (literal_next_atom position) ∧
      (∀ task : Fin (position + 1) → ℂ, type_of% (literal_next_recovery position task)) ∧
      (normal bound).targetRuntime.tick.next.current.visit.current = (runtimePayload position).nativeWrite.target := by
  exact ⟨source_payload_is_original bound, (realization bound).operationAt,
    (fun actor => ⟨sourceWord_actual_birth bound actor, sourceWord_actual_point bound actor, whole_recorded _ bound actor,
      recordedRestriction_nextRead _ bound actor, sourceWord_recorded_ne_zero bound actor, recordedQuery_ne_zero bound actor,
      recovered_actor_before_normal bound actor⟩),
    whole_pmf _ bound, whole_on_actual_support _ bound, next_conditional_recorded _ bound,
    (fun task actor => ⟨original_transfer_on_record _ bound task actor, prime_transfer_on_record bound task actor⟩),
    original_field_transfer_on_record _ bound, whole_at_acquisition_normal _ bound, original_field_at_acquisition_normal _ bound,
    acquisition_stage_count bound, last_record_is_target bound, last_record_is_generated_birth bound,
    canonical_next_after_records bound, (normal bound).target_factorizes, literal_next_atom _, literal_next_recovery _,
    runtime_current_next (completionDepth sourceOwner bound + 1)⟩

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
