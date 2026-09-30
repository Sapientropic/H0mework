import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertCompression
import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertResidual
import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertSquare

/-! The original time transfer, full source history, dictionary square and paid compression cost reach the same ledger and next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance consumerWordsMeasurable (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := Dynamic.Hilbert.measurable depth
local instance consumerFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) := fieldBorel nativeStep (rawWords depth)

theorem original_time_information_consumed (depth : Nat) (task : Fin (depth + 1) → ℂ) :
    type_of% (observation_rawWords (depth + 1)) ∧ type_of% (Actor.current_pmf (depth + 1) depth) ∧
      type_of% (Actor.next_pmf (depth + 1) depth) ∧
      (∀ index : Fin (depth + 1), type_of% (Actor.originalRead_actual (depth + 1) depth index) ∧
        type_of% (next_read_actual (depth + 1) depth index) ∧ type_of% (original_next_recovery (depth + 1) depth task index)) ∧
      (∀ value : SourceOwnedObservationHistory.Space nativeStep (rawWords (depth + 1)) CanonicalUnitArithmeticRoot.initialCurrent depth,
        type_of% (sourceTime_transfer_original (depth + 1) CanonicalUnitArithmeticRoot.initialCurrent depth value) ∧
        type_of% (sourceTime_original_energy (depth + 1) CanonicalUnitArithmeticRoot.initialCurrent depth value) ∧
        type_of% (time_dictionary_residual depth CanonicalUnitArithmeticRoot.initialCurrent depth value) ∧
        ∀ atom : Field nativeStep (rawWords (depth + 1)),
        ∀ supported : atom ∈ (SourceWeightedRecovery.observed (historyPMF depth) (Actor.nextRead (depth + 1) depth)).support,
        type_of% (Actor.original_transfer_formula (depth + 1) depth value atom supported)) ∧
      (∀ value : SourceWeightedRecovery.Space (wordLaw (depth + 1) CanonicalUnitArithmeticRoot.initialCurrent depth),
        type_of% (sourceTime_original_residual (depth + 1) CanonicalUnitArithmeticRoot.initialCurrent depth value) ∧
        type_of% (sourceTime_original_residual_norm (depth + 1) CanonicalUnitArithmeticRoot.initialCurrent depth value) ∧
        type_of% (sourceTime_original_reconstruction (depth + 1) CanonicalUnitArithmeticRoot.initialCurrent depth value)) ∧
      type_of% (time_dictionary_square depth CanonicalUnitArithmeticRoot.initialCurrent depth) ∧
      type_of% (time_dictionary_adjoint depth CanonicalUnitArithmeticRoot.initialCurrent depth) ∧
      type_of% (literal_next_atom depth) ∧ type_of% (literal_next_recovery depth task) ∧
      type_of% (Dynamic.dynamic_words_consumed depth) :=
  ⟨observation_rawWords (depth + 1), Actor.current_pmf (depth + 1) depth, Actor.next_pmf (depth + 1) depth,
    (fun index => ⟨Actor.originalRead_actual (depth + 1) depth index, next_read_actual (depth + 1) depth index,
      original_next_recovery (depth + 1) depth task index⟩),
    (fun value => ⟨sourceTime_transfer_original (depth + 1) _ depth value, sourceTime_original_energy (depth + 1) _ depth value,
      time_dictionary_residual depth _ depth value, Actor.original_transfer_formula (depth + 1) depth value⟩),
    (fun value => ⟨sourceTime_original_residual (depth + 1) _ depth value, sourceTime_original_residual_norm (depth + 1) _ depth value,
      sourceTime_original_reconstruction (depth + 1) _ depth value⟩),
    time_dictionary_square depth _ depth, time_dictionary_adjoint depth _ depth,
    literal_next_atom depth, literal_next_recovery depth task, Dynamic.dynamic_words_consumed depth⟩

theorem original_snapshot_information_consumed (owner : GlobalParentOwner) (decoder : ParentCarrier → ℂ) :
    let depth := Dynamic.Hilbert.collisionBound owner
    type_of% (original_snapshot_cost owner (depth + 1) decoder) ∧
      type_of% (original_snapshot_cost_positive owner (depth + 1) decoder) ∧
      (∀ index : Fin (depth + 1), type_of% (original_next_recovery (depth + 1) depth (Dynamic.Hilbert.clockTask depth) index)) ∧
      type_of% (literal_next_atom depth) ∧ type_of% (literal_next_recovery depth (Dynamic.Hilbert.clockTask depth)) ∧
      (let runtime := runtimeAt depth
       let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
       HEq stage.wholeLedgerWriteBack
         (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
       stage.next.current = stage.activated.nextCurrent) := by
  have source := (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (Dynamic.Hilbert.collisionBound owner))).factorizes
  exact ⟨original_snapshot_cost owner _ decoder, original_snapshot_cost_positive owner _ decoder,
    original_next_recovery _ _ (Dynamic.Hilbert.clockTask _), literal_next_atom _, literal_next_recovery _ (Dynamic.Hilbert.clockTask _),
    source.2.2⟩

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
