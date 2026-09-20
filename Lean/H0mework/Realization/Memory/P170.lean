/-
  Proposition 170: finite-to-continuous forgetting bridge.

  P141-P143 describe finite heterogeneous mixtures.  P147 proves that the
  continuous gamma-rate mixture is a shifted-power tail.  This file supplies
  the formal bridge shape between them: a finite exponential-rate mixture can
  be connected to the continuous gamma mixture by an exact quadrature,
  approximation, or convergence certificate; once such a certificate is
  supplied, P147 transports it to the shifted-power target.

  This is intentionally not an LLN theorem.  It is the reusable target that an
  LLN, deterministic quadrature, or runtime empirical certificate must feed.
-/

import H0mework.Realization.Relations.P147
import Mathlib.Topology.Basic

open scoped Real Topology

noncomputable section

namespace FiniteContinuousForgettingBridge

/-- A finite mixture of exponential forgetting rates at real time `time`. -/
def finiteExponentialRateMixture
    {Agent : Type*} [Fintype Agent]
    (amplitude rate : Agent -> ℝ) (time : ℝ) : ℝ :=
  ∑ i : Agent, amplitude i * Real.exp (-(rate i) * time)

/-- Exact finite-to-continuous bridge: if a finite quadrature / empirical
mixture equals the normalized gamma mixture at a time, then it equals the
shifted-power target at that time. -/
theorem finiteMixture_eq_shifted_power_of_eq_normalizedGammaLaplace
    {Agent : Type*} [Fintype Agent]
    (amplitude rateFn : Agent -> ℝ)
    {shape gammaRate time : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate) (htime : 0 ≤ time)
    (hbridge :
      finiteExponentialRateMixture amplitude rateFn time =
        GammaMixtureForgetting.normalizedGammaLaplace shape gammaRate time) :
    finiteExponentialRateMixture amplitude rateFn time =
      (1 + time / gammaRate) ^ (-shape) := by
  rw [hbridge]
  exact GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
    hshape hrate htime

/-- Approximate finite-to-continuous bridge: an error bound against the
normalized gamma mixture is the same error bound against the shifted-power
target. -/
theorem finiteMixture_abs_error_to_shifted_power_le
    {Agent : Type*} [Fintype Agent]
    (amplitude rateFn : Agent -> ℝ)
    {shape gammaRate time ε : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate) (htime : 0 ≤ time)
    (hbound :
      |finiteExponentialRateMixture amplitude rateFn time -
        GammaMixtureForgetting.normalizedGammaLaplace shape gammaRate time| ≤ ε) :
    |finiteExponentialRateMixture amplitude rateFn time -
        (1 + time / gammaRate) ^ (-shape)| ≤ ε := by
  rwa [← GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
    hshape hrate htime]

/-- Pointwise convergence bridge: any finite-mixture approximation sequence
that converges to the continuous gamma mixture also converges to the
shifted-power target. -/
theorem finiteMixture_tendsto_shifted_power_of_tendsto_gamma
    {Index Agent : Type*} [Fintype Agent]
    {l : Filter Index}
    (amplitude rateFn : Index -> Agent -> ℝ)
    {shape gammaRate time : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate) (htime : 0 ≤ time)
    (hconv :
      Filter.Tendsto
        (fun n : Index =>
          finiteExponentialRateMixture (amplitude n) (rateFn n) time)
        l
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate time))) :
    Filter.Tendsto
      (fun n : Index =>
        finiteExponentialRateMixture (amplitude n) (rateFn n) time)
      l
      (𝓝 ((1 + time / gammaRate) ^ (-shape))) := by
  simpa [GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
    hshape hrate htime] using hconv

/-!
  Summary:
  - P170 does not pretend to prove sampling theory.
  - It closes the formal interface: finite heterogeneous mixtures can be
    transported to the continuous shifted-power theorem by exact, bounded-error,
    or pointwise-convergence certificates.
  - A future LLN theorem should produce `hconv`; runtime empirical harnesses
    can produce `hbound`.
-/


end FiniteContinuousForgettingBridge
