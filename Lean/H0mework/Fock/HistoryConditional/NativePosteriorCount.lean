import H0mework.Fock.HistoryConditional.NativeObserversUpdate
import H0mework.Probability.Information.Conditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativePosterior

open SourceConditionalNativeObservers (generate seed advance generated_next)
variable {Key : Type*} [DecidableEq Key]

theorem count_sum (read : Nat → Key) (bound : Nat) (value : Key) :
    (generate read bound value).1 = ∑ index : Fin (bound + 1), if read index.val = value then 1 else 0 := by
  induction bound with
  | zero =>
      change (seed read value).1 = ∑ index : Fin 1, if read index.val = value then 1 else 0
      rw [Fin.sum_univ_one]
      by_cases same : value = read 0
      · simp only [seed, if_pos same, Fin.val_zero, if_pos same.symm]
      · simp only [seed, if_neg same, Fin.val_zero, if_neg (Ne.symm same)]
  | succ bound previous =>
      rw [generated_next, advance, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      by_cases same : value = read (bound + 1)
      · simp only [if_pos same, if_pos same.symm, previous]
      · simp only [if_neg same, if_neg (Ne.symm same), previous, add_zero]

theorem count_fibre (read : Nat → Key) (bound : Nat) (value : Key) :
    (generate read bound value).1 = (SourceUniformFibreVariance.fibre bound (fun index => read index.val) value).card := by
  rw [count_sum, Finset.sum_boole]
  rfl

theorem count_positive (read : Nat → Key) (bound : Nat) (value : Key)
    (actor : Fin (bound + 1)) (present : read actor.val = value) :
    0 < (generate read bound value).1 := by
  rw [count_fibre]
  exact Finset.card_pos.mpr ⟨actor, (SourceUniformFibreVariance.fibre_mem _ _ _ _).mpr present⟩

end SourceConditionalNativePosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
