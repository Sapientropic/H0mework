import H0mework.Fock.SourceHistoryClock.BinomialPrefixSource

/-! A three-integer state runs the generated update and restores the original square consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Prefix

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

theorem recover_next (samples : Window) : recover (next samples) = action (recover samples) :=
  recover_window (action (recover samples))

theorem recover_iterate (steps : Nat) (samples : Window) :
    recover ((next ^ steps) samples) = (action ^ steps) (recover samples) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
      rw [pow_succ', pow_succ']
      change recover (next ((next ^ steps) samples)) = action ((action ^ steps) (recover samples))
      rw [recover_next, previous]

def decode (depth : Nat) (observed : Window) (index : Fin 3) : ℂ :=
  (pastSquare (depth + 1) (recover ((next ^ index.val) (next observed))) : ℂ)

theorem decode_actual (depth : Nat) (index : Fin 3) :
    decode depth (currentSamples depth) index = Runtime.Actor.History.Clock.sourceSquare 2 index := by
  rw [decode, next_samples, recover_iterate]
  exact source_square_from_samples depth index

theorem exact_finite_cost (depth : Nat) :
    error (historyPMF 2) (fun index : Fin 3 => (next ^ index.val) (next (currentSamples depth)))
      (Runtime.Actor.History.Clock.sourceSquare 2)
      (fun observed => (pastSquare (depth + 1) (recover observed) : ℂ)) = 0 := by
  change (∑ index : Fin 3, (historyPMF 2 index).toReal *
    ‖Runtime.Actor.History.Clock.sourceSquare 2 index - decode depth (currentSamples depth) index‖ ^ 2) = 0
  simp only [decode_actual, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

end
end SourceBinomialClock.Prefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
