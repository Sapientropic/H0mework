import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic

/-!
# A finite countdown for a clocked receiver state

This file supplies the small termination lemma used by the concrete ADC
microcontroller.  It introduces no execution carrier: the caller provides its
actual step and remaining-tick rank.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

/-- Once rank zero is stable and every positive-rank step strictly decreases
the rank, every clock budget at least as large as the current rank reaches
rank zero. -/
theorem finiteADCMicroCountdown_eq_zero_of_le
    {State : Type*} (step : State → State) (remaining : State → Nat)
    (zeroStable : ∀ state, remaining state = 0 → remaining (step state) = 0)
    (strictDecrease : ∀ state, 0 < remaining state →
      remaining (step state) < remaining state)
    (state : State) (ticks : Nat) (enough : remaining state ≤ ticks) :
    remaining ((step^[ticks]) state) = 0 := by
  induction ticks generalizing state with
  | zero =>
      simpa only [Function.iterate_zero_apply] using Nat.eq_zero_of_le_zero enough
  | succ ticks inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      apply inductionHypothesis (state := step state)
      by_cases done : remaining state = 0
      · rw [zeroStable state done]
        exact Nat.zero_le ticks
      · have enough' : remaining state ≤ Nat.succ ticks := by
          simpa only [Nat.succ_eq_add_one] using enough
        exact Nat.le_of_lt_succ
          (Nat.lt_of_lt_of_le (strictDecrease state (Nat.pos_of_ne_zero done)) enough')

/-- The rank carried by a state itself is a sufficient exact clock budget. -/
theorem finiteADCMicroCountdown_eq_zero
    {State : Type*} (step : State → State) (remaining : State → Nat)
    (zeroStable : ∀ state, remaining state = 0 → remaining (step state) = 0)
    (strictDecrease : ∀ state, 0 < remaining state →
      remaining (step state) < remaining state)
    (state : State) :
    remaining ((step^[remaining state]) state) = 0 :=
  finiteADCMicroCountdown_eq_zero_of_le step remaining zeroStable strictDecrease
    state (remaining state) (Nat.le_refl _)

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
