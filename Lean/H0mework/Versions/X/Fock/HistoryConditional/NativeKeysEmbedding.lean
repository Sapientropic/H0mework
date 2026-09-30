import H0mework.Versions.X.Fock.HistoryConditional.NativeKeysWord

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeKeys

open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open scoped Classical
noncomputable section

def keyTable (bound : Nat) (state : State bound) : ZMod 2 →₀ (Nat × (Nat →₀ ℚ)) :=
  Finsupp.onFinset Finset.univ (fun key => ((state key).1, word bound (state key).2)) (fun key _ => Finset.mem_univ key)

def embed (bound depth : Nat) (state : State bound) : SourceConditionalRationalStream.Table :=
  (keyTable bound state).mapDomain (observed depth)

theorem embed_at (bound depth : Nat) (state : State bound) (key : ZMod 2) :
    embed bound depth state (observed depth key) = ((state key).1, word bound (state key).2) := by
  rw [embed, Finsupp.mapDomain_apply (observed_injective depth), keyTable, Finsupp.onFinset_apply]

theorem embed_outside (bound depth : Nat) (state : State bound) (value : Field parity)
    (outside : value ∉ Set.range (observed depth)) : embed bound depth state value = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ outside

theorem seed_embed (depth : Nat) : embed 0 depth seed = SourceConditionalRationalStream.seed depth := by
  apply Finsupp.ext
  intro value
  by_cases inside : value ∈ Set.range (observed depth)
  · obtain ⟨key, rfl⟩ := inside
    rw [embed_at, SourceConditionalRationalStream.seed, Finsupp.single_apply, source_observed]
    have comparison : observed depth (0 : ZMod 2) = observed depth key ↔ key = 0 := by
      rw [(observed_injective depth).eq_iff]
      exact eq_comm
    have actualZero : ((0 : Fin (0 + 1)).val : ZMod 2) = 0 := by norm_num
    rw [actualZero, comparison]
    by_cases zero : key = 0
    · subst key
      simp only [seed, SourceConditionalNativeObservers.seed, ite_true, word, LinearMap.coe_mk, AddHom.coe_mk]
      change (1, ∑ i : Fin 1, (1 : ℚ) • SourceConditionalRationalStream.sourceWord 0 i) = (1, SourceConditionalRationalStream.sourceWord 0 0)
      rw [Fin.sum_univ_one, one_smul]
    · simp only [seed, SourceConditionalNativeObservers.seed, Nat.cast_zero, if_neg zero]
      change (0, word 0 0) = (0, 0)
      rw [map_zero]
  · rw [embed_outside _ _ _ _ inside, SourceConditionalRationalStream.seed, Finsupp.single_apply]
    have absent : SourceConditionalInventory.observation 0 depth 0 ≠ value := by
      rw [source_observed]
      exact fun same => inside ⟨0, same⟩
    exact (if_neg absent).symm

theorem advance_embed (bound depth : Nat) (previous : State bound) :
    embed (bound + 1) depth (advance bound previous) =
      SourceConditionalRationalStream.advance bound depth (embed bound depth previous) := by
  apply Finsupp.ext
  intro value
  by_cases inside : value ∈ Set.range (observed depth)
  · obtain ⟨key, rfl⟩ := inside
    rw [embed_at, SourceConditionalRationalStream.advance, Finsupp.update_apply, birth_observed, embed_at]
    have comparison : observed depth key = observed depth ((bound + 1 : Nat) : ZMod 2) ↔ key = ((bound + 1 : Nat) : ZMod 2) :=
      (observed_injective depth).eq_iff
    simp only [comparison, advance, SourceConditionalNativeObservers.advance]
    by_cases hit : key = ((bound + 1 : Nat) : ZMod 2)
    · subst key
      simp only [ite_true, word_updated]
    · simp only [if_neg hit, word_retained, embed_at]
  · rw [embed_outside _ _ _ _ inside, SourceConditionalRationalStream.advance, Finsupp.update_apply]
    have absent : value ≠ SourceConditionalInventory.bornObservation bound depth := by
      rw [birth_observed]
      exact fun same => inside ⟨_, same.symm⟩
    rw [if_neg absent, embed_outside _ _ _ _ inside]

theorem generated_embed (bound depth : Nat) : embed bound depth (generate bound) = SourceConditionalRationalStream.generate depth bound := by
  induction bound with
  | zero => exact seed_embed depth
  | succ bound previous => rw [generated_next, advance_embed, previous, SourceConditionalRationalStream.generated_next]

end
end SourceConditionalNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
