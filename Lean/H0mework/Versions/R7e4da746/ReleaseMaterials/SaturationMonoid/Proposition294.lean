import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.Proposition291
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Proposition 294: affine-pullback complete monotonicity for shifted-power time

P291 proved complete monotonicity for the positive-base coordinate

`x ↦ x^(-shape)`.

The actual forgetting curve is the affine pullback along the positive time
coordinate `x = 1 + scale * t`:

`t ↦ (1 + scale * t)^(-shape)`.

This file closes that boundary.  First, it proves a reusable all-order derivative
law for scaling the input, using Mathlib's derivative rule for `f (c*x)` that
does not require a global differentiability hypothesis.  Then it combines that
with translation invariance and P291's Pochhammer formula to get the exact
time-coordinate derivative formula.  The alternating signs are therefore
positive on nonnegative time whenever `shape > 0` and `scale > 0`.
-/

open scoped Real

noncomputable section

namespace ShiftedPowerCompleteMonotonicity

open Real
open ShiftedPowerEffectiveRate

/-! ## Affine pullback of all iterated derivatives -/

/-- THEOREM 1: scaling the input by `c` multiplies the `n`-th derivative by
`c^n`.  This formulation uses `deriv^[n]` directly and therefore inherits
Lean/Mathlib's fallback semantics at nondifferentiability points. -/
theorem iter_deriv_comp_mul_left_real
    (f : ℝ → ℝ) (c : ℝ) (n : ℕ) :
    deriv^[n] (fun x : ℝ => f (c * x)) =
      fun x : ℝ => c ^ n * deriv^[n] f (c * x) := by
  induction n with
  | zero =>
      ext x
      simp
  | succ n ih =>
      ext x
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih]
      rw [deriv_const_mul_field]
      rw [deriv_comp_mul_left]
      simp only [smul_eq_mul]
      ring

/-- THEOREM 2: translating the input by `a` leaves the `n`-th derivative
unchanged, evaluated at the translated point. -/
theorem iter_deriv_comp_const_add_real
    (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    deriv^[n] (fun x : ℝ => f (a + x)) =
      fun x : ℝ => deriv^[n] f (a + x) := by
  simpa [iteratedDeriv_eq_iterate] using
    (iteratedDeriv_comp_const_add (𝕜 := ℝ) (F := ℝ) n f a)

/-- THEOREM 3: affine input `a + c*x` combines translation with the `c^n`
scaling factor. -/
theorem iter_deriv_comp_const_add_mul_real
    (f : ℝ → ℝ) (a c : ℝ) (n : ℕ) :
    deriv^[n] (fun x : ℝ => f (a + c * x)) =
      fun x : ℝ => c ^ n * deriv^[n] f (a + c * x) := by
  have hscale :=
    iter_deriv_comp_mul_left_real (fun y : ℝ => f (a + y)) c n
  have hshift :=
    iter_deriv_comp_const_add_real f a n
  ext x
  have hx := congrFun hscale x
  rw [hx]
  rw [hshift]

/-! ## Shifted-power time curve -/

/-- THEOREM 4: the actual time-coordinate shifted-power curve has the closed
Pochhammer derivative formula. -/
theorem iter_deriv_shiftedPowerRetention_eq
    (shape scale time : ℝ) (n : ℕ) :
    deriv^[n]
        (fun t : ℝ =>
          shiftedPowerRetention shape scale t) time =
      (-1 : ℝ) ^ n * scale ^ n * risingShape shape n *
        (1 + scale * time) ^ (-shape - (n : ℝ)) := by
  change deriv^[n]
      (fun t : ℝ => positiveBasePowerRetention shape (1 + scale * t)) time =
    (-1 : ℝ) ^ n * scale ^ n * risingShape shape n *
      (1 + scale * time) ^ (-shape - (n : ℝ))
  have haff :=
    congrFun
      (iter_deriv_comp_const_add_mul_real
        (fun x : ℝ => positiveBasePowerRetention shape x) 1 scale n)
      time
  rw [haff]
  rw [iter_deriv_positiveBasePowerRetention_eq]
  ring

/-- Project-local complete monotonicity predicate on nonnegative real time. -/
def CompletelyMonotoneOnNonnegativeTime (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1 : ℝ) ^ n * deriv^[n] f t

/-- THEOREM 5: the shifted-power time curve is completely monotone on
nonnegative time whenever `shape > 0` and `scale > 0`. -/
theorem shiftedPowerRetention_completelyMonotoneOnNonnegativeTime
    {shape scale : ℝ} (hshape : 0 < shape) (hscale : 0 < scale) :
    CompletelyMonotoneOnNonnegativeTime
      (fun t : ℝ => shiftedPowerRetention shape scale t) := by
  intro n t ht
  rw [iter_deriv_shiftedPowerRetention_eq]
  have hsign : 0 ≤ (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n) := by
    simpa [pow_two] using sq_nonneg ((-1 : ℝ) ^ n)
  have hscalePow : 0 ≤ scale ^ n := by
    exact pow_nonneg (le_of_lt hscale) n
  have hrising : 0 ≤ risingShape shape n := by
    exact le_of_lt (risingShape_pos hshape n)
  have hbase : 0 < 1 + scale * t := by
    nlinarith [mul_nonneg (le_of_lt hscale) ht]
  have hrpow : 0 ≤ (1 + scale * t) ^ (-shape - (n : ℝ)) := by
    exact le_of_lt (Real.rpow_pos_of_pos hbase _)
  have hprod :
      0 ≤ ((((-1 : ℝ) ^ n * ((-1 : ℝ) ^ n)) * scale ^ n) *
          risingShape shape n *
            (1 + scale * t) ^ (-shape - (n : ℝ))) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hsign hscalePow) hrising) hrpow
  convert hprod using 1
  ring

/-- THEOREM 6: the P291 positive-base certificate and the actual time-coordinate
certificate agree under affine pullback. -/
theorem shiftedPowerCompleteMonotone_and_LaplaceWitness
    {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    CompletelyMonotoneOnNonnegativeTime
        (fun t : ℝ => (1 + t / rate) ^ (-shape)) ∧
      HasGammaLaplaceBernsteinWitness
        (fun t : ℝ => (1 + t / rate) ^ (-shape)) shape rate := by
  have hscale : 0 < rate⁻¹ := inv_pos.mpr hrate
  constructor
  · intro n t ht
    have hmono :=
      shiftedPowerRetention_completelyMonotoneOnNonnegativeTime
        (shape := shape) (scale := rate⁻¹) hshape hscale n t ht
    have hfun :
        (fun t : ℝ => shiftedPowerRetention shape rate⁻¹ t) =
          (fun t : ℝ => (1 + t / rate) ^ (-shape)) := by
      ext τ
      simp [ShiftedPowerEffectiveRate.shiftedPowerRetention, div_eq_mul_inv, mul_comm]
    rw [← hfun]
    exact hmono
  · exact shiftedPowerRetention_hasGammaLaplaceBernsteinWitness hshape hrate

end ShiftedPowerCompleteMonotonicity
