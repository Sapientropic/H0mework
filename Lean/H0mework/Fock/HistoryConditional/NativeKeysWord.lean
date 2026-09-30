import H0mework.Fock.HistoryConditional.NativeKeysArray

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeKeys

noncomputable section

theorem source_single (bound : Nat) (index : Fin (bound + 1)) :
    SourceConditionalRationalStream.sourceWord bound index = Finsupp.single (index.val + 1) (1 : ℚ) := by
  apply SourceConditionalRationalStream.embed_word_injective
  rw [SourceConditionalRationalStream.source_embed, SourceConditionalWordStream.source_single,
    SourceConditionalRationalStream.embedWord, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  norm_num

def word (bound : Nat) : (Fin (bound + 1) → ℚ) →ₗ[ℚ] (Nat →₀ ℚ) where
  toFun row := ∑ index : Fin (bound + 1), row index • SourceConditionalRationalStream.sourceWord bound index
  map_add' left right := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar row := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem word_coefficient (bound : Nat) (row : Fin (bound + 1) → ℚ) (actor : Fin (bound + 1)) :
    word bound row (actor.val + 1) = row actor := by
  classical
  simp only [word, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, source_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single actor]
  · simp only [ite_true, smul_eq_mul, mul_one]
  · intro other _ different
    rw [if_neg (fun same => different (Fin.ext (Nat.add_right_cancel same))), smul_zero]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem source_retained (bound : Nat) (index : Fin (bound + 1)) :
    SourceConditionalRationalStream.sourceWord (bound + 1) index.castSucc = SourceConditionalRationalStream.sourceWord bound index := rfl

theorem word_append (bound : Nat) (row : Fin (bound + 1) → ℚ) (last : ℚ) :
    word (bound + 1) (Fin.lastCases last row) = word bound row + last • SourceConditionalRationalStream.bornWord bound := by
  change (∑ index : Fin (bound + 2), (Fin.lastCases last row index : ℚ) • SourceConditionalRationalStream.sourceWord (bound + 1) index) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, source_retained]
  rfl

theorem word_retained (bound : Nat) (row : Fin (bound + 1) → ℚ) :
    word (bound + 1) (Fin.lastCases 0 row) = word bound row := by
  rw [word_append, zero_smul, add_zero]

private theorem scalar_update (count : Nat) (previous added : Nat →₀ ℚ) :
    ((count : ℚ) / (count + 1 : Nat)) • previous + ((count + 1 : Nat) : ℚ)⁻¹ • added =
      previous + ((count + 1 : Nat) : ℚ)⁻¹ • (added - previous) := by
  have nonzero : ((count + 1 : Nat) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero count
  have scale : ((count : ℚ) / (count + 1 : Nat)) = 1 - ((count + 1 : Nat) : ℚ)⁻¹ := by
    push_cast
    field_simp
    ring
  rw [scale, sub_smul, one_smul, smul_sub]
  abel

theorem word_updated (bound count : Nat) (row : Fin (bound + 1) → ℚ) :
    word (bound + 1) (Fin.lastCases ((count + 1 : Nat) : ℚ)⁻¹
      (fun index => ((count : ℚ) / (count + 1 : Nat)) * row index)) =
      word bound row + ((count + 1 : Nat) : ℚ)⁻¹ • (SourceConditionalRationalStream.bornWord bound - word bound row) := by
  rw [word_append]
  change word bound (((count : ℚ) / (count + 1 : Nat)) • row) + _ = _
  rw [map_smul]
  exact scalar_update count _ _

end
end SourceConditionalNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
