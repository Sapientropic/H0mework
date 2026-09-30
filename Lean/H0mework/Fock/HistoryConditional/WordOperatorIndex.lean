import H0mework.Fock.HistoryConditional.WordAffineEquation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledWordOperator

theorem slope_positive (word : List (Option Nat)) : 0 < (SourceCopyWordAffine.compile word).1 := by
  induction word with
  | nil => decide
  | cons letter rest previous =>
      cases letter with
      | none => exact previous
      | some materialIndex => exact Nat.mul_pos previous (Nat.succ_pos materialIndex)

theorem index_exact (word : List (Option Nat)) (state : Nat) :
    SourceCopyWordAffine.execute (SourceCopyWordAffine.compile word) state + 1 =
      (SourceCopyWordAffine.compile word).1 * (state + 1) + (SourceCopyWordAffine.compile word).2 := by
  rw [SourceCopyWordAffine.execute_original]
  exact SourceCopyWordAffine.equation word state

theorem index_injective (word : List (Option Nat)) :
    Function.Injective (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile word)) := by
  intro left right same
  have effect := congrArg (fun state => state + 1) same
  rw [index_exact, index_exact] at effect
  exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left (slope_positive word) (Nat.add_right_cancel effect))

theorem index_range (word : List (Option Nat)) (state : Nat) :
    state ∈ Set.range (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile word)) ↔
      (SourceCopyWordAffine.compile word).2 < state + 1 ∧
      (SourceCopyWordAffine.compile word).1 ∣ state + 1 - (SourceCopyWordAffine.compile word).2 := by
  let a := (SourceCopyWordAffine.compile word).1
  let b := (SourceCopyWordAffine.compile word).2
  have positive : 0 < a := slope_positive word
  constructor
  · rintro ⟨prior, rfl⟩
    rw [index_exact]
    have product : 0 < a * (prior + 1) := Nat.mul_pos positive (Nat.succ_pos prior)
    refine ⟨by change b < a * (prior + 1) + b; omega, ?_⟩
    rw [Nat.add_sub_cancel]
    exact dvd_mul_right _ _
  · rintro ⟨bLower, divides⟩
    obtain ⟨count, generated⟩ := divides
    have nonzero : count ≠ 0 := by
      intro zero
      rw [zero, Nat.mul_zero] at generated
      omega
    refine ⟨count - 1, ?_⟩
    apply Nat.add_right_cancel (m := 1)
    rw [index_exact, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr nonzero)]
    omega

end SourceCompiledWordOperator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
