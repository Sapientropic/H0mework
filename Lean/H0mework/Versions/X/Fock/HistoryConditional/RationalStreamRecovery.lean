import H0mework.Versions.X.Fock.HistoryConditional.RationalStreamUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRationalStream

open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (observation count)
open scoped Classical
noncomputable section

theorem embed_word_injective : Function.Injective embedWord := by
  intro left right same
  apply Finsupp.ext
  intro index
  have coordinate := congrArg (fun word : Nat →₀ ℂ => word index) same
  change (left index : ℂ) = (right index : ℂ) at coordinate
  exact Rat.cast_injective coordinate

theorem embed_injective : Function.Injective embed := by
  intro left right same
  apply Finsupp.ext
  intro value
  have entry := congrArg (fun table : SourceConditionalWordStream.Table => table value) same
  change (((left value).1 : ℝ), embedWord (left value).2) = (((right value).1 : ℝ), embedWord (right value).2) at entry
  apply Prod.ext
  · have counts : ((left value).1 : ℝ) = ((right value).1 : ℝ) :=
      congrArg (fun item : ℝ × (Nat →₀ ℂ) => item.1) entry
    exact_mod_cast counts
  · apply embed_word_injective
    exact congrArg (fun item : ℝ × (Nat →₀ ℂ) => item.2) entry

theorem support_embed (table : Table) : (embed table).support = table.support := by
  ext value
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  change (((table value).1 : ℝ), embedWord (table value).2) ≠ 0 ↔ table value ≠ 0
  constructor
  · intro nonzero zero
    apply nonzero
    rw [zero]
    simp only [Prod.fst_zero, Prod.snd_zero, Nat.cast_zero, map_zero]
    rfl
  · intro nonzero zero
    apply nonzero
    apply Prod.ext
    · have counts : ((table value).1 : ℝ) = 0 := congrArg (fun item : ℝ × (Nat →₀ ℂ) => item.1) zero
      exact_mod_cast counts
    · apply embed_word_injective
      exact (congrArg (fun item : ℝ × (Nat →₀ ℂ) => item.2) zero).trans (map_zero embedWord).symm

theorem support_exact (bound depth : Nat) :
    (generate depth bound).support = SourceUniformFibreVariance.outputs bound (observation bound depth) := by
  rw [← support_embed, generated_embed, SourceConditionalWordStream.support_exact]

theorem count_exact (bound depth : Nat) (value : Field parity) :
    (generate depth bound value).1 = (SourceUniformFibreVariance.fibre bound (observation bound depth) value).card := by
  have mapped := congrArg (fun table : SourceConditionalWordStream.Table => (table value).1) (generated_embed bound depth)
  change ((generate depth bound value).1 : ℝ) = (SourceConditionalWordStream.generate depth bound value).1 at mapped
  have original := congrArg (fun item : ℝ × SourceJointClockGraph.Carrier => item.1)
    (SourceConditionalWordStream.generated_entry bound depth value)
  change (SourceConditionalWordStream.generate depth bound value).1 = count bound depth value at original
  have same := mapped.trans original
  rw [SourceConditionalInnovation.count_fibre] at same
  exact_mod_cast same

theorem coefficient_embed (bound depth : Nat) (value : Field parity) (index : Nat) :
    ((generate depth bound value).2 index : ℂ) = (SourceConditionalWordStream.generate depth bound value).2 index := by
  have same := congrArg (fun table : SourceConditionalWordStream.Table => (table value).2 index) (generated_embed bound depth)
  exact same

theorem coefficient_posterior (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) (actor : Fin (bound + 1)) :
    ((generate depth bound value).2 (actor.val + 1) : ℝ) =
      (SourceConditionalInventory.conditional bound depth value supported actor).toReal := by
  have original := (coefficient_embed bound depth value (actor.val + 1)).trans
    (SourceConditionalWordStream.word_coefficient bound depth value supported actor)
  have realPart := congrArg Complex.re original
  simpa only [Complex.ratCast_re, Complex.ofReal_re] using realPart

theorem complete_count (bound depth : Nat) :
    (∑ value ∈ (generate depth bound).support, (generate depth bound value).1) = bound + 1 := by
  rw [support_exact]
  simp only [count_exact]
  exact SourceUniformFibreVariance.fibre_card_sum bound (observation bound depth)

end
end SourceConditionalRationalStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
