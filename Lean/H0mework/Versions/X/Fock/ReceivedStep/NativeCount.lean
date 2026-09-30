import H0mework.Versions.X.Fock.RationalWindow.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

def rowCount (bound : Nat) (row : Fin (bound + 1) → ℚ) : Nat :=
  ∑ actor, if row actor = 0 then 0 else 1

theorem count_source {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (key : Key) :
    rowCount bound (SourceConditionalNativeObservers.generate read bound key).2 =
      (SourceConditionalNativeObservers.generate read bound key).1 := by
  rw [rowCount, SourceConditionalNativePosterior.count_sum]
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceConditionalNativePosterior.weight_fibre]
  by_cases present : read actor.val = key
  · have nonzero : ((SourceConditionalNativeObservers.generate read bound key).1 : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (SourceConditionalNativePosterior.count_positive read bound key actor present).ne'
    simp only [if_pos present, inv_eq_zero, if_neg nonzero]
  · simp only [if_neg present, ite_true]

end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
