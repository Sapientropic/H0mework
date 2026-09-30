import H0mework.Versions.X.Fock.HistoryConditional.RationalStreamSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRationalStream

open SourceGeneratedRuntimeHistoryProbability
open SourceConditionalInventory (bornObservation)
open scoped Classical
noncomputable section

theorem embed_correction (count : Nat) (word : Nat →₀ ℚ) :
    embedWord (((count : ℚ) + 1)⁻¹ • word) =
      (((count : ℝ) + 1 : ℝ) : ℂ)⁻¹ • embedWord word := by
  rw [map_smul, ← algebraMap_smul ℂ]
  simp only [map_inv₀, map_add, map_natCast, map_one,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]

theorem advance_embed (bound depth : Nat) (previous : Table) :
    embed (advance bound depth previous) = SourceConditionalWordStream.advance bound depth (embed previous) := by
  apply Finsupp.ext
  intro value
  by_cases same : value = bornObservation bound depth
  · subst value
    simp only [embed, advance, Finsupp.mapRange_apply, Finsupp.update_apply, SourceConditionalWordStream.advance,
      ite_true, map_add, embed_correction, map_sub, born_embed, Nat.cast_add, Nat.cast_one]
  · simp only [embed, advance, Finsupp.mapRange_apply, Finsupp.update_apply, SourceConditionalWordStream.advance, if_neg same]

theorem generated_embed (bound depth : Nat) : embed (generate depth bound) = SourceConditionalWordStream.generate depth bound := by
  induction bound with
  | zero => exact seed_embed depth
  | succ bound previous => rw [generated_next, advance_embed, previous, SourceConditionalWordStream.generated_next]

end
end SourceConditionalRationalStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
