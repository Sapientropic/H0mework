import H0mework.Fock.HistoryModel.DynamicHilbertCompression

/-! Original full history, source action, material, ledger and literal next consume the paid information equation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceConditionalHistory
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open SourcePrimeObservationDelay
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance (depth : Nat) : UniformSpace (Complete.Carrier depth) := uniform depth
local instance (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := measurable depth
local instance (depth : Nat) : BorelSpace (Complete.Carrier depth) := ⟨rfl⟩
local instance (depth : Nat) : T2Space (Complete.Carrier depth) := field_t2 depth

theorem dynamic_information_consumed (depth : Nat) (task : Fin (depth + 2) → ℂ) :
    type_of% (actor_law (depth + 1)) ∧ type_of% (original_law depth (depth + 1)) ∧
      type_of% (original_law (depth + 1) (depth + 1)) ∧ type_of% (previous_preserving depth (depth + 1)) ∧
      type_of% (original_pullback depth (depth + 1)) ∧ type_of% (original_transfer depth (depth + 1)) ∧
      (∀ value : Space (historyPMF (depth + 1)), type_of% (original_residual depth (depth + 1) value) ∧
        type_of% (original_residual_energy depth (depth + 1) value) ∧
        type_of% (original_reconstruction depth (depth + 1) value) ∧
        type_of% (complete_residual_zero depth (depth + 1) value)) ∧
      (∀ value : Space (law (depth + 1) (depth + 1)), type_of% (restriction_residual_zero depth (depth + 1) value) ∧
        type_of% (restriction_recovery depth (depth + 1) value)) ∧
      (∀ atom : Complete.Carrier depth, ∀ supported : atom ∈ (law depth (depth + 1)).support,
        type_of% (full_original_conditional depth (depth + 1) atom supported) ∧
        type_of% (conditional_weights depth (depth + 1) task atom supported)) ∧
      (∀ atom : Complete.Carrier depth, ∀ supported : atom ∈ (SourceConditionalHistory.observed (law (depth + 1) (depth + 1)) (previous depth)).support,
        type_of% (whole_actor_mixture depth (depth + 1) atom supported)) ∧
      (∀ index : Fin (depth + 2), type_of% (complete_recovery depth (depth + 1) task index)) ∧
      type_of% (actual_new_atom depth) ∧ type_of% (actual_old_atom depth) ∧
      (∀ supported : read depth (depth + 1) (Fin.last (depth + 1)) ∈ (law depth (depth + 1)).support,
        ∀ index : Fin (depth + 2), type_of% (actual_whole_support depth supported index)) ∧
      type_of% (actual_next_recovery depth task) ∧ type_of% (dynamic_words_consumed depth) :=
  ⟨actor_law (depth + 1), original_law depth (depth + 1), original_law (depth + 1) (depth + 1),
    previous_preserving depth (depth + 1), original_pullback depth (depth + 1), original_transfer depth (depth + 1),
    (fun value => ⟨original_residual depth (depth + 1) value, original_residual_energy depth (depth + 1) value,
      original_reconstruction depth (depth + 1) value, complete_residual_zero depth (depth + 1) value⟩),
    (fun value => ⟨restriction_residual_zero depth (depth + 1) value, restriction_recovery depth (depth + 1) value⟩),
    (fun atom supported => ⟨full_original_conditional depth (depth + 1) atom supported,
      conditional_weights depth (depth + 1) task atom supported⟩),
    whole_actor_mixture depth (depth + 1), complete_recovery depth (depth + 1) task,
    actual_new_atom depth, actual_old_atom depth, actual_whole_support depth, actual_next_recovery depth task,
    dynamic_words_consumed depth⟩

theorem snapshot_recovery_consumed (owner : GlobalParentOwner) (decoder : ParentCarrier → ℂ) :
    let depth := firstState owner 0
    type_of% (actual_snapshot_collision owner) ∧ type_of% (collision_indices_distinct owner) ∧
      type_of% (source_birth_zero owner 0 0 le_rfl) ∧ type_of% (source_multiplicity_increases owner 0 0) ∧
      type_of% (compressed_clock_cost owner depth decoder) ∧ type_of% (complete_clock_cost_zero owner depth) ∧
      type_of% (compressed_clock_gap owner depth decoder) ∧ type_of% (no_snapshot_reconstruction owner depth) ∧
      type_of% (actual_next_recovery depth (clockTask (collisionBound owner))) ∧
      (let runtime := runtimeAt depth
       let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
       HEq stage.wholeLedgerWriteBack
         (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
       stage.next.current = stage.activated.nextCurrent) := by
  have source := (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (firstState owner 0))).factorizes
  exact ⟨actual_snapshot_collision owner, collision_indices_distinct owner, source_birth_zero owner 0 0 le_rfl,
    source_multiplicity_increases owner 0 0, compressed_clock_cost owner _ decoder, complete_clock_cost_zero owner _,
    compressed_clock_gap owner _ decoder, no_snapshot_reconstruction owner _,
    actual_next_recovery _ (clockTask (collisionBound owner)), source.2.2⟩

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
