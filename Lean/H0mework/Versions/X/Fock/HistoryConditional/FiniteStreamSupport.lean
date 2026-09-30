import H0mework.Versions.X.Fock.HistoryConditional.FiniteStreamSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalFiniteStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (observation bornObservation count)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem support_iff (bound depth : Nat) (value : Field parity) :
    value ∈ (generate depth bound).support ↔ value ∈ ((historyPMF bound).map (observation bound depth)).support := by
  rw [Finsupp.mem_support_iff, generated_entry]
  constructor
  · intro nonzero
    by_contra missing
    apply nonzero
    rw [SourceConditionalInnovation.count_zero bound depth value missing,
      SourceConditionalInnovation.decoder_missing bound depth value missing]
    rfl
  · intro supported zero
    have nonzero := (SourceConditionalInnovation.count_positive bound depth value supported).ne'
    exact nonzero (congrArg Prod.fst zero)

theorem support_exact (bound depth : Nat) :
    (generate depth bound).support = SourceUniformFibreVariance.outputs bound (observation bound depth) := by
  ext value
  rw [support_iff]
  exact ⟨SourceUniformFibreVariance.supported_output bound _ value,
    SourceUniformFibreVariance.output_supported bound _ value⟩

theorem support_next (bound depth : Nat) :
    (generate depth (bound + 1)).support = insert (bornObservation bound depth) (generate depth bound).support := by
  ext value
  rw [support_iff, Finset.mem_insert, support_iff, SourceConditionalInventory.new_support_iff]
  exact or_comm

theorem entry_count (bound depth : Nat) (value : Field parity) :
    (generate depth bound value).1 = (SourceUniformFibreVariance.fibre bound (observation bound depth) value).card := by
  rw [generated_entry]
  exact SourceConditionalInnovation.count_fibre bound depth value

theorem complete_count (bound depth : Nat) :
    (∑ value ∈ (generate depth bound).support, (generate depth bound value).1) = (bound + 1 : ℝ) := by
  rw [support_exact]
  simp only [entry_count]
  exact_mod_cast SourceUniformFibreVariance.fibre_card_sum bound (observation bound depth)

theorem slot_count (bound depth : Nat) :
    (generate depth bound).support.card = (SourceUniformFibreVariance.outputs bound (observation bound depth)).card := by
  rw [support_exact]

theorem table_current_next (runtime : LivingRuntimeState process) (depth : Nat) :
    generate depth (inventoryBound runtime.tick.next) = advance (inventoryBound runtime) depth (generate depth (inventoryBound runtime)) := by
  rw [SourceActualImageStep.next_bound, generated_next]

end
end SourceConditionalFiniteStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
