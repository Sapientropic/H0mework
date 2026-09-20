/-
  Proposition 146: saturation-fed fast decay plus shifted-power slow tail.

  The empirical forgetting track now has to use the corrected boundary:
  single-channel exponential/geometric decay is the special case; heterogeneous
  multi-channel systems, including a biological individual with multiple
  internal traces, can already produce power-like behavior.

  P139/P140 gave the algebraic two-phase skeleton:

      fast(n) = C₁ * (1 - σ)^n
      slow(n) = C₂ * tail(n)

  and P143 proved that the shifted-power tail

      tail(n) = (1 + b n)^(-m)

  is already incompatible with a single geometric first-three fit.  This file
  packages the exact discrete bridge consumed by the Igarashi-style empirical
  comparison: a saturation/noisy-OR fast channel plus a shifted-power slow
  tail has the two-phase shape, inherits the switching-point majority theorem,
  and collapses to P143's obstruction when the fast channel is absent.

  Boundary: this is still discrete ordered-field algebra.  It does not prove
  analytic real `exp`, real-valued `t^(-α)`, AIC optimality, or the continuous
  Murre-Chessa gamma-mixture / Laplace-transform theorem.
-/

import H0mework.Realization.Memory.P140
import H0mework.Realization.Memory.P143

namespace TwoPhaseEmpiricalBridge

open TwoPhaseRetention
open TwoPhaseSaturationBridge

/-! ## Saturation fast channel plus shifted-power slow tail -/

/-- The shifted-power slow tail used by the executable gamma-mixture harness. -/
def shiftedPowerSlowTail
    {α : Type*} [DivisionSemiring α]
    (scale : α) (exponent : Nat) : Nat -> α :=
  fun n => shiftedPowerRetention scale exponent n

/-- A discrete Igarashi-style two-phase skeleton:

`C₁ * (1 - σ)^n + C₂ * (1 + b n)^(-m)`.
-/
def h1ShiftedPowerSignal
    {α : Type*} [Field α]
    (fastAmplitude σ slowAmplitude scale : α)
    (exponent n : Nat) : α :=
  h1TwoPhaseSignal fastAmplitude σ slowAmplitude
    (shiftedPowerSlowTail scale exponent) n

/-- THEOREM 1: the packaged signal is exactly the component formula
`C₁ * (1 - σ)^n + C₂ * (1 + b n)^(-m)`. -/
theorem h1ShiftedPowerSignal_eq_components
    {α : Type*} [Field α]
    (fastAmplitude σ slowAmplitude scale : α)
    (exponent n : Nat) :
    h1ShiftedPowerSignal fastAmplitude σ slowAmplitude scale exponent n =
      fastAmplitude * (1 - σ) ^ n +
        slowAmplitude * shiftedPowerRetention scale exponent n := by
  rfl

/-- THEOREM 2: the packaged signal is P139's discrete two-phase skeleton with
fast keep-rate `1 - σ` and shifted-power slow tail. -/
theorem h1ShiftedPowerSignal_eq_discreteTwoPhase
    {α : Type*} [Field α]
    (fastAmplitude σ slowAmplitude scale : α)
    (exponent n : Nat) :
    h1ShiftedPowerSignal fastAmplitude σ slowAmplitude scale exponent n =
      discreteTwoPhase fastAmplitude (1 - σ) slowAmplitude
        (shiftedPowerSlowTail scale exponent) n := by
  rfl

/-! ## Noisy-OR composition remains the fast-channel law -/

/-- THEOREM 3: composing two saturation rates by noisy-OR makes the fast
channel keep-rate the product of the two residual keep-rates.  The shifted
power slow tail is untouched. -/
theorem h1ShiftedPowerSignal_composed_rate
    {α : Type*} [Field α]
    (fastAmplitude slowAmplitude scale σ₁ σ₂ : α)
    (exponent n : Nat) :
    h1ShiftedPowerSignal fastAmplitude (satOrField σ₁ σ₂)
        slowAmplitude scale exponent n =
      fastAmplitude * ((1 - σ₁) * (1 - σ₂)) ^ n +
        slowAmplitude * shiftedPowerRetention scale exponent n := by
  unfold h1ShiftedPowerSignal h1TwoPhaseSignal saturationFastChannel
    shapedSlow shiftedPowerSlowTail shiftedPowerRetention
  rw [keep_of_satOrField]

/-! ## Switching-point bridge -/

/-- THEOREM 4: in the saturation-plus-shifted-power model, the slow tail
dominates the fast saturation channel exactly when it contributes more than
half of the total signal. -/
theorem h1ShiftedPower_slow_switch_iff_majority
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (fastAmplitude σ slowAmplitude scale : α)
    (exponent n : Nat) :
    saturationFastChannel fastAmplitude σ n <
        slowAmplitude * shiftedPowerRetention scale exponent n <->
      h1ShiftedPowerSignal fastAmplitude σ slowAmplitude scale exponent n <
        (2 : α) *
          (slowAmplitude * shiftedPowerRetention scale exponent n) := by
  simpa [h1ShiftedPowerSignal, shiftedPowerSlowTail, shapedSlow]
    using h1TwoPhase_slow_switch_iff_majority
      (fastAmplitude := fastAmplitude) (σ := σ)
      (slowAmplitude := slowAmplitude)
      (slowTail := shiftedPowerSlowTail scale exponent) (n := n)

/-- THEOREM 5: symmetrically, the fast saturation channel dominates the shifted
power slow tail exactly when the fast channel contributes more than half of the
total signal. -/
theorem h1ShiftedPower_fast_switch_iff_majority
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (fastAmplitude σ slowAmplitude scale : α)
    (exponent n : Nat) :
    slowAmplitude * shiftedPowerRetention scale exponent n <
        saturationFastChannel fastAmplitude σ n <->
      h1ShiftedPowerSignal fastAmplitude σ slowAmplitude scale exponent n <
        (2 : α) * saturationFastChannel fastAmplitude σ n := by
  simpa [h1ShiftedPowerSignal, shiftedPowerSlowTail, shapedSlow]
    using h1TwoPhase_fast_switch_iff_majority
      (fastAmplitude := fastAmplitude) (σ := σ)
      (slowAmplitude := slowAmplitude)
      (slowTail := shiftedPowerSlowTail scale exponent) (n := n)

/-! ## Shifted-power obstruction as the zero-fast boundary -/

/-- THEOREM 6: multiplying a shifted-power tail by a positive amplitude
preserves the positive first-three residual. -/
theorem scaledShiftedPower_first_three_residual_pos
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {amplitude scale : α} {exponent : Nat}
    (hamplitude : 0 < amplitude)
    (hscale : 0 < scale) (hexponent : 0 < exponent) :
    0 <
      (amplitude * shiftedPowerRetention scale exponent 0) *
          (amplitude * shiftedPowerRetention scale exponent 2) -
        (amplitude * shiftedPowerRetention scale exponent 1) ^ 2 := by
  have htail :=
    shiftedPowerRetention_first_three_residual_pos
      (scale := scale) (exponent := exponent) hscale hexponent
  have hamp_sq : 0 < amplitude ^ 2 := sq_pos_of_pos hamplitude
  have hfactor :
      (amplitude * shiftedPowerRetention scale exponent 0) *
          (amplitude * shiftedPowerRetention scale exponent 2) -
        (amplitude * shiftedPowerRetention scale exponent 1) ^ 2 =
        amplitude ^ 2 *
          (shiftedPowerRetention scale exponent 0 *
              shiftedPowerRetention scale exponent 2 -
            (shiftedPowerRetention scale exponent 1) ^ 2) := by
    ring
  rw [hfactor]
  exact mul_pos hamp_sq htail

/-- THEOREM 7: a positive scaled shifted-power tail cannot be explained by a
single geometric first-three fit. -/
theorem scaledShiftedPower_refutes_single_geometric_first_three
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {amplitude scale : α} {exponent : Nat}
    (hamplitude : 0 < amplitude)
    (hscale : 0 < scale) (hexponent : 0 < exponent) :
    ¬ FitsSingleGeometricFirstThree
      (fun n => amplitude * shiftedPowerRetention scale exponent n) := by
  have hpos :=
    scaledShiftedPower_first_three_residual_pos
      (amplitude := amplitude) (scale := scale)
      (exponent := exponent) hamplitude hscale hexponent
  have hres :
      (amplitude * shiftedPowerRetention scale exponent 0) *
          (amplitude * shiftedPowerRetention scale exponent 2) -
        (amplitude * shiftedPowerRetention scale exponent 1) ^ 2 ≠ 0 :=
    ne_of_gt hpos
  intro hfit
  exact hres (moment_zero_of_fitsSingleGeometricFirstThree hfit)

/-- THEOREM 8: when the fast channel is absent, the two-phase package reduces
to the scaled shifted-power tail, hence inherits P143's single-geometric
obstruction. -/
theorem h1ShiftedPower_zero_fast_refutes_single_geometric_first_three
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {slowAmplitude scale σ : α} {exponent : Nat}
    (hamplitude : 0 < slowAmplitude)
    (hscale : 0 < scale) (hexponent : 0 < exponent) :
    ¬ FitsSingleGeometricFirstThree
      (fun n => h1ShiftedPowerSignal (0 : α) σ
        slowAmplitude scale exponent n) := by
  simpa [h1ShiftedPowerSignal, h1TwoPhaseSignal, saturationFastChannel,
    shapedSlow, shiftedPowerSlowTail] using
      scaledShiftedPower_refutes_single_geometric_first_three
        (amplitude := slowAmplitude) (scale := scale)
        (exponent := exponent) hamplitude hscale hexponent

/-!
  Summary:
  - P146 gives the exact discrete algebraic shape matching the empirical
    `C₁e^(-βt) + C₂t^(-α)` story without pretending to formalize analytic
    exponentials or statistical model comparison.
  - The fast component is generated by saturation/noisy-OR residual keep-rate.
  - The slow component can be the shifted-power tail already certified by P143.
  - The Igarashi-style switch predicate is inherited from P139/P140.
-/


end TwoPhaseEmpiricalBridge
