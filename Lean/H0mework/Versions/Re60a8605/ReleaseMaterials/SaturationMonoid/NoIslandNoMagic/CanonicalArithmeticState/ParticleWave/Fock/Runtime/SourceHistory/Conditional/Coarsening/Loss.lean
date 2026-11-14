import H0mework.Fock.ClockCoarsening.Source

/-! Actual pulse coarsening gives the exact clock cost of every original finite history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePulseCoarsening

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

private theorem split_clock_squares (bound : Nat) (atZero atRest : ℂ) :
    (∑ point : Fin (bound + 1), ‖(point.val : ℂ) - (if point.val = 0 then atZero else atRest)‖ ^ 2) =
      ‖atZero‖ ^ 2 + (bound : ℝ) *
        (((bound : ℝ) ^ 2 - 1) / 12 + ‖(((bound + 1 : ℝ) / 2 : ℝ) : ℂ) - atRest‖ ^ 2) := by
  induction bound with
  | zero => simp
  | succ bound previous =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [previous, if_neg (Nat.succ_ne_zero bound)]
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
      push_cast
      ring

theorem current_clock_error (bound : Nat) (decoder : ZMod 2 → ℂ) :
    error (historyPMF bound) (observe bound) (clockTask bound) decoder =
      (bound : ℝ) * (bound - 1) / 12 +
      ‖decoder 1‖ ^ 2 / (bound + 1 : ℝ) +
      (bound : ℝ) / (bound + 1 : ℝ) * ‖(((bound + 1 : ℝ) / 2 : ℝ) : ℂ) - decoder 0‖ ^ 2 := by
  simp only [error, clock_actual, observe_actual, apply_ite decoder,
    historyPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, split_clock_squares]
  push_cast
  field_simp
  ring

theorem next_clock_error (bound : Nat) (decoder : ZMod 2 → ℂ) :
    error (historyPMF bound) (nextObserve bound) (clockTask bound) decoder =
      (bound : ℝ) * (bound + 2) / 12 + ‖(((bound : ℝ) / 2 : ℝ) : ℂ) - decoder 0‖ ^ 2 := by
  simpa only [error, clock_actual, next_observe_source, forget, mul_one, one_mul, zero_add,
    one_pow, Complex.ofReal_natCast] using
    ObservationRefinement.uniform_clock_error bound 0 1 (decoder 0)

def currentDecoder (bound : Nat) (observed : ZMod 2) : ℂ :=
  if observed = 1 then 0 else (((bound + 1 : ℝ) / 2 : ℝ) : ℂ)

def nextDecoder (bound : Nat) : ZMod 2 → ℂ := fun _ => (((bound : ℝ) / 2 : ℝ) : ℂ)

theorem current_attains (bound : Nat) :
    error (historyPMF bound) (observe bound) (clockTask bound) (currentDecoder bound) =
      (bound : ℝ) * (bound - 1) / 12 := by
  rw [current_clock_error]
  simp [currentDecoder]

theorem next_attains (bound : Nat) :
    error (historyPMF bound) (nextObserve bound) (clockTask bound) (nextDecoder bound) =
      (bound : ℝ) * (bound + 2) / 12 := by
  rw [next_clock_error]
  simp [nextDecoder]

theorem clock_coarsening_loss (bound : Nat) :
    error (historyPMF bound) (nextObserve bound) (clockTask bound) (nextDecoder bound) =
      error (historyPMF bound) (observe bound) (clockTask bound) (currentDecoder bound) + (bound : ℝ) / 4 := by
  rw [next_attains, current_attains]
  ring

end
end SourcePulseCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
