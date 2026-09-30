import H0mework.Fock.HistoryConditional.NativePosteriorCount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativePosterior

open SourceConditionalNativeObservers (generate seed advance generated_next)
open SourceGeneratedRuntimeHistoryProbability (historyPMF)
variable {Key : Type*} [DecidableEq Key]

theorem weight_fibre (read : Nat → Key) (bound : Nat) (value : Key) (actor : Fin (bound + 1)) :
    (generate read bound value).2 actor = if read actor.val = value then ((generate read bound value).1 : ℚ)⁻¹ else 0 := by
  induction bound with
  | zero =>
      have actorZero : actor.val = 0 := by omega
      change (seed read value).2 actor = if read actor.val = value then ((seed read value).1 : ℚ)⁻¹ else 0
      rw [actorZero]
      by_cases same : value = read 0
      · simp only [seed, if_pos same, if_pos same.symm, Nat.cast_one, inv_one]
      · simp only [seed, if_neg same, if_neg (Ne.symm same)]
  | succ bound previous =>
      rw [generated_next]
      by_cases hit : value = read (bound + 1)
      · simp only [advance, if_pos hit]
        refine Fin.lastCases ?_ (fun actor => ?_) actor
        · simp only [Fin.lastCases_last, Fin.val_last, if_pos hit.symm]
        · simp only [Fin.lastCases_castSucc, Fin.val_castSucc, previous actor]
          by_cases present : read actor.val = value
          · simp only [if_pos present]
            have positive := count_positive read bound value actor present
            have nonzero : ((generate read bound value).1 : ℚ) ≠ 0 :=
              Nat.cast_ne_zero.mpr positive.ne'
            field_simp
          · simp only [if_neg present, mul_zero]
      · simp only [advance, if_neg hit]
        refine Fin.lastCases ?_ (fun actor => ?_) actor
        · simp only [Fin.lastCases_last, Fin.val_last, if_neg (Ne.symm hit)]
        · simpa only [Fin.lastCases_castSucc, Fin.val_castSucc] using previous actor

theorem posterior (read : Nat → Key) (bound : Nat) (value : Key)
    (supported : value ∈ ((historyPMF bound).map (fun actor : Fin (bound + 1) => read actor.val)).support)
    (actor : Fin (bound + 1)) :
    ((generate read bound value).2 actor : ℝ) =
      (SourceConditionalHistory.conditional (historyPMF bound) (fun index => read index.val) value supported actor).toReal := by
  rw [weight_fibre, SourceUniformFibreVariance.conditional_weight]
  by_cases present : read actor.val = value
  · rw [if_pos present, if_pos ((SourceUniformFibreVariance.fibre_mem _ _ _ _).mpr present)]
    push_cast
    rw [count_fibre]
  · rw [if_neg present, if_neg (fun inside => present ((SourceUniformFibreVariance.fibre_mem _ _ _ _).mp inside))]
    norm_num

end SourceConditionalNativePosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
