import H0mework.Realization.Relations.P147
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Proposition 183: shifted-power effective-rate dynamics

P147 proves the analytic gamma/Laplace bridge:

`normalizedGammaLaplace shape rate time = (1 + time / rate)^(-shape)`.

This file records the dynamical reading used by the empirical track.  For a
shifted-power curve

`C(t) = (1 + b*t)^(-c)`,

the canonical log-retention coordinate is

`log C(t) = -c * log (1 + b*t)`,

and its instantaneous effective decay rate is

`λ(t) = - d/dt log C(t) = c*b / (1 + b*t)`.

Boundary: this proves the calculus of the shifted-power family.  It does not
fit data, choose a changepoint model, or prove that a concrete runtime trace
population has gamma-distributed rates.
-/

namespace ShiftedPowerEffectiveRate

open Real

noncomputable section

/-! ## Definitions -/

/-- Shifted-power retention `C(t) = (1 + scale*t)^(-shape)`. -/
def shiftedPowerRetention (shape scale time : ℝ) : ℝ :=
  (1 + scale * time) ^ (-shape)

/-- Canonical log-retention coordinate for shifted-power forgetting. -/
def shiftedPowerLog (shape scale time : ℝ) : ℝ :=
  -shape * Real.log (1 + scale * time)

/-- Instantaneous effective decay rate `λ(t) = c*b / (1 + b*t)`. -/
def shiftedPowerEffectiveRate (shape scale time : ℝ) : ℝ :=
  shape * scale / (1 + scale * time)

/-! ## Log-coordinate bridge -/

/-- THEOREM 1: on a positive base, the ordinary log of the shifted-power
retention agrees with the canonical log-retention coordinate. -/
theorem log_shiftedPowerRetention_eq_shiftedPowerLog
    {shape scale time : ℝ}
    (hbase : 0 < 1 + scale * time) :
    Real.log (shiftedPowerRetention shape scale time) =
      shiftedPowerLog shape scale time := by
  unfold shiftedPowerRetention shiftedPowerLog
  rw [Real.log_rpow hbase (-shape)]

/-! ## Effective-rate calculus -/

/-- THEOREM 2: the derivative of the canonical shifted-power log coordinate. -/
theorem hasDerivAt_shiftedPowerLog
    {shape scale time : ℝ}
    (hbase : 1 + scale * time ≠ 0) :
    HasDerivAt
      (fun x : ℝ => shiftedPowerLog shape scale x)
      (-(shape * scale) / (1 + scale * time))
      time := by
  have hinner :
      HasDerivAt (fun x : ℝ => 1 + scale * x) scale time := by
    simpa [mul_comm] using
      ((hasDerivAt_id' time).const_mul scale).const_add (1 : ℝ)
  have hlog :
      HasDerivAt
        (fun x : ℝ => Real.log (1 + scale * x))
        (scale / (1 + scale * time))
        time := by
    exact hinner.log hbase
  have hmul :
      HasDerivAt
        (fun x : ℝ => -shape * Real.log (1 + scale * x))
        ((-shape) * (scale / (1 + scale * time)))
        time := hlog.const_mul (-shape)
  convert hmul using 1
  · ext x
    simp [shiftedPowerLog]
  · field_simp

/-- THEOREM 3: the derivative has the closed form
`-(c*b)/(1+b*t)`. -/
theorem deriv_shiftedPowerLog_eq
    {shape scale time : ℝ}
    (hbase : 1 + scale * time ≠ 0) :
    deriv (fun x : ℝ => shiftedPowerLog shape scale x) time =
      -(shape * scale) / (1 + scale * time) :=
  (hasDerivAt_shiftedPowerLog (shape := shape) (scale := scale)
    (time := time) hbase).deriv

/-- THEOREM 4: the effective rate is the negative derivative of the
log-retention coordinate. -/
theorem shiftedPowerEffectiveRate_eq_neg_deriv_log
    {shape scale time : ℝ}
    (hbase : 1 + scale * time ≠ 0) :
    shiftedPowerEffectiveRate shape scale time =
      -deriv (fun x : ℝ => shiftedPowerLog shape scale x) time := by
  rw [deriv_shiftedPowerLog_eq (shape := shape) (scale := scale)
    (time := time) hbase]
  unfold shiftedPowerEffectiveRate
  ring

/-! ## Parameter consequences -/

/-- THEOREM 5: at time zero, the effective rate is `shape*scale`. -/
theorem shiftedPowerEffectiveRate_zero
    (shape scale : ℝ) :
    shiftedPowerEffectiveRate shape scale 0 = shape * scale := by
  unfold shiftedPowerEffectiveRate
  ring

/-- THEOREM 6: the characteristic time `1/scale` is the half-rate point. -/
theorem shiftedPowerEffectiveRate_inv_scale
    {shape scale : ℝ}
    (hscale : scale ≠ 0) :
    shiftedPowerEffectiveRate shape scale scale⁻¹ =
      shape * scale / 2 := by
  unfold shiftedPowerEffectiveRate
  field_simp [hscale]
  ring

/-- THEOREM 7: for positive shape/scale and nonnegative time, the effective
rate is positive. -/
theorem shiftedPowerEffectiveRate_pos
    {shape scale time : ℝ}
    (hshape : 0 < shape) (hscale : 0 < scale) (htime : 0 ≤ time) :
    0 < shiftedPowerEffectiveRate shape scale time := by
  unfold shiftedPowerEffectiveRate
  exact div_pos (mul_pos hshape hscale)
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (le_of_lt hscale) htime))

/-- THEOREM 8: along nonnegative time, the shifted-power effective rate is
nonincreasing. -/
theorem shiftedPowerEffectiveRate_anti_mono
    {shape scale t₁ t₂ : ℝ}
    (hshape : 0 ≤ shape) (hscale : 0 ≤ scale)
    (ht₁ : 0 ≤ t₁) (hle : t₁ ≤ t₂) :
    shiftedPowerEffectiveRate shape scale t₂ ≤
      shiftedPowerEffectiveRate shape scale t₁ := by
  have ht₂ : 0 ≤ t₂ := le_trans ht₁ hle
  have hnum : 0 ≤ shape * scale := mul_nonneg hshape hscale
  have hden₁ : 0 < 1 + scale * t₁ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hscale ht₁)
  have hden₂ : 0 < 1 + scale * t₂ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hscale ht₂)
  have hden_le : 1 + scale * t₁ ≤ 1 + scale * t₂ := by
    gcongr
  unfold shiftedPowerEffectiveRate
  exact div_le_div_of_nonneg_left hnum hden₁ hden_le

/-!
  Summary:
  - P183 turns P147's shifted-power closed form into an instantaneous
    effective-rate theorem.
  - The characteristic time `1/scale` is now a Lean theorem: the effective rate
    is halved there.
  - This gives the cross-scale-switching discussion a precise parameter to
    compare, without claiming any empirical model has already been selected.
-/


end

end ShiftedPowerEffectiveRate
