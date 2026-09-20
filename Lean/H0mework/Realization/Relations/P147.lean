/-
  Proposition 147: the continuous gamma-mixture bridge.

  P143 proved that a shifted-power tail has the local first-three obstruction.
  P146 packaged the discrete two-phase shape consumed by the Igarashi-style
  empirical track.  This file closes the next mathematical gap: the shifted
  power tail is not just an arbitrary slow-tail input.  It is the Laplace
  transform of a gamma-shaped mixture of exponential/geometric decay rates.

  In real terms, for shape `a > 0`, rate `r > 0`, and time `t >= 0`,

      ∫₀∞ x^(a-1) exp (-(r+t)x) dx = (r+t)^(-a) Γ(a).

  Multiplying by the gamma-density normalizer `r^a / Γ(a)` gives

      r^a * (r+t)^(-a),

  i.e. the shifted-power retention shape `(1 + t/r)^(-a)` up to the standard
  positive-base rpow algebra.

  Boundary: this is the continuous gamma/Laplace identity.  It still does not
  prove empirical AIC optimality, finite-sample estimation, or the sleep /
  consolidation mechanism behind a particular changepoint.
-/

import H0mework.Realization.RelaxationFlow.P146
import Mathlib.MeasureTheory.Integral.Gamma

open Set
open scoped Real

noncomputable section

namespace GammaMixtureForgetting

/-! ## Gamma-shaped exponential-rate mixtures -/

/-- Unnormalized gamma-rate mixture of exponential forgetting at time `time`.
The shape is `shape`, the base rate is `rate`, and the integrand has the
combined rate `rate + time`. -/
def unnormalizedGammaLaplace (shape rate time : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ),
    x ^ (shape - 1) * Real.exp (-(rate + time) * x)

/-- THEOREM 1: the core gamma/Laplace identity behind shifted-power forgetting.
-/
theorem unnormalizedGammaLaplace_eq
    {shape rate time : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htime : 0 ≤ time) :
    unnormalizedGammaLaplace shape rate time =
      (rate + time) ^ (-shape) * Real.Gamma shape := by
  have hq : -1 < shape - 1 := by linarith
  have hcombined : 0 < rate + time := add_pos_of_pos_of_nonneg hrate htime
  have h :=
    integral_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (q := shape - 1) (b := rate + time)
      zero_lt_one hq hcombined
  simpa [unnormalizedGammaLaplace, Real.rpow_one] using h

/-- Gamma-density normalizer for a positive shape/rate pair. -/
def gammaLaplaceNormalizer (shape rate : ℝ) : ℝ :=
  rate ^ shape * (Real.Gamma shape)⁻¹

/-- Normalized gamma-rate mixture of exponential forgetting. -/
def normalizedGammaLaplace (shape rate time : ℝ) : ℝ :=
  gammaLaplaceNormalizer shape rate *
    unnormalizedGammaLaplace shape rate time

/-- THEOREM 2: after normalization, the gamma-rate mixture is exactly the
shifted-power retention factor `rate^shape * (rate + time)^(-shape)`. -/
theorem normalizedGammaLaplace_eq_rate_mul_shifted
    {shape rate time : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htime : 0 ≤ time) :
    normalizedGammaLaplace shape rate time =
      rate ^ shape * (rate + time) ^ (-shape) := by
  have hgamma : Real.Gamma shape ≠ 0 :=
    (Real.Gamma_pos_of_pos hshape).ne'
  rw [normalizedGammaLaplace, gammaLaplaceNormalizer,
    unnormalizedGammaLaplace_eq hshape hrate htime]
  field_simp [hgamma]

/-- THEOREM 3: the same normalized mixture is the standard shifted-power
factor `(1 + time / rate)^(-shape)`. -/
theorem normalizedGammaLaplace_eq_shifted_power
    {shape rate time : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htime : 0 ≤ time) :
    normalizedGammaLaplace shape rate time =
      (1 + time / rate) ^ (-shape) := by
  have hcombined : 0 < rate + time := add_pos_of_pos_of_nonneg hrate htime
  rw [normalizedGammaLaplace_eq_rate_mul_shifted hshape hrate htime]
  have hone :
      1 + time / rate = (rate + time) / rate := by
    field_simp [hrate.ne']
  rw [hone]
  rw [Real.div_rpow (le_of_lt hcombined) (le_of_lt hrate)]
  rw [Real.rpow_neg (le_of_lt hcombined)]
  rw [Real.rpow_neg (le_of_lt hrate)]
  field_simp [Real.rpow_pos_of_pos hrate shape]

/-!
  Summary:
  - P147 closes the analytic bridge that P143/P146 deliberately left open.
  - A gamma-shaped distribution over exponential forgetting rates has a
    shifted-power Laplace transform.
  - This validates the corrected forgetting-track statement at the mathematical
    mechanism level: power-like forgetting can arise from heterogeneous rate
    mixtures inside one agent or across many agents.

  Still outside this theorem:
  - empirical model comparison / AIC;
  - finite-sample parameter estimation;
  - sleep/consolidation mechanisms for observed changepoints;
  - runtime evidence that a particular AIppocampus trace population follows a
    gamma rate distribution.
-/


end GammaMixtureForgetting
