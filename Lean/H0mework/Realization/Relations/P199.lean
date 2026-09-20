import H0mework.Realization.Memory.P170

/-!
# Proposition 199: finite-mixture-to-gamma bridge certificates

P170 supplied reusable transport lemmas: if an external theorem/certificate
shows that a finite exponential-rate mixture converges to the normalized gamma
mixture, then P147 transports that convergence to the shifted-power target.

This file formalizes the certificate object itself.  It is deliberately not an
LLN or order-statistics theorem; it is the typed obligation an LLN, quadrature
scheme, or runtime empirical harness must satisfy.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## All-time convergence certificate -/

/-- A reusable certificate that a finite exponential-rate mixture sequence
converges pointwise to the normalized gamma-rate mixture for every nonnegative
time. -/
structure FiniteToGammaConvergenceCertificate
    (Index Agent : Type*) [Fintype Agent] (l : Filter Index) where
  amplitude : Index → Agent → ℝ
  rateFn : Index → Agent → ℝ
  shape : ℝ
  gammaRate : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  finite_tendsto_gamma :
    ∀ {time : ℝ}, 0 ≤ time →
      Tendsto
        (fun n : Index =>
          FiniteContinuousForgettingBridge.finiteExponentialRateMixture
            (amplitude n) (rateFn n) time)
        l
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate time))

/-- THEOREM 1: an all-time finite→gamma certificate transports to all-time
shifted-power convergence. -/
theorem finiteToGammaCertificate_tendsto_shiftedPower
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaConvergenceCertificate Index Agent l)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun n : Index =>
        FiniteContinuousForgettingBridge.finiteExponentialRateMixture
          (cert.amplitude n) (cert.rateFn n) time)
      l
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) :=
  FiniteContinuousForgettingBridge.finiteMixture_tendsto_shifted_power_of_tendsto_gamma
      (amplitude := cert.amplitude) (rateFn := cert.rateFn)
      (shape := cert.shape) (gammaRate := cert.gammaRate) (time := time)
      cert.shape_pos cert.gammaRate_pos htime
      (cert.finite_tendsto_gamma htime)

/-- THEOREM 2: the same certificate can be read at a fixed observation time as
P170's original pointwise bridge. -/
theorem finiteToGammaCertificate_fixedTime_recovers_P170_bridge
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaConvergenceCertificate Index Agent l)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun n : Index =>
        FiniteContinuousForgettingBridge.finiteExponentialRateMixture
          (cert.amplitude n) (cert.rateFn n) time)
      l
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) :=
  finiteToGammaCertificate_tendsto_shiftedPower cert htime

/-! ## Finite observation-grid certificate -/

/-- A finite grid of observation times.  This is the form an empirical harness
usually owns: a finite family of times, each with nonnegative-time evidence. -/
structure FiniteObservationGrid where
  Time : Type*
  inst : Fintype Time
  time : Time → ℝ
  nonneg : ∀ τ : Time, 0 ≤ time τ

attribute [instance] FiniteObservationGrid.inst

/-- THEOREM 3: an all-time finite→gamma certificate gives shifted-power
convergence on every point of a finite observation grid. -/
theorem finiteToGammaCertificate_grid_tendsto_shiftedPower
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaConvergenceCertificate Index Agent l)
    (grid : FiniteObservationGrid) :
    ∀ τ : grid.Time,
      Tendsto
        (fun n : Index =>
          FiniteContinuousForgettingBridge.finiteExponentialRateMixture
            (cert.amplitude n) (cert.rateFn n) (grid.time τ))
        l
        (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  intro τ
  exact finiteToGammaCertificate_tendsto_shiftedPower cert (grid.nonneg τ)

/-! ## Bounded-error certificate -/

/-- A finite bounded-error certificate against the normalized gamma mixture at
one observation time. -/
structure FiniteToGammaErrorCertificate
    (Agent : Type*) [Fintype Agent] where
  amplitude : Agent → ℝ
  rateFn : Agent → ℝ
  shape : ℝ
  gammaRate : ℝ
  time : ℝ
  ε : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  time_nonneg : 0 ≤ time
  error_to_gamma :
    |FiniteContinuousForgettingBridge.finiteExponentialRateMixture
        amplitude rateFn time -
      GammaMixtureForgetting.normalizedGammaLaplace shape gammaRate time| ≤ ε

/-- THEOREM 4: a bounded-error finite→gamma certificate transports to the same
bounded error against the shifted-power target. -/
theorem finiteToGammaErrorCertificate_shiftedPower_bound
    {Agent : Type*} [Fintype Agent]
    (cert : FiniteToGammaErrorCertificate Agent) :
    |FiniteContinuousForgettingBridge.finiteExponentialRateMixture
        cert.amplitude cert.rateFn cert.time -
      (1 + cert.time / cert.gammaRate) ^ (-cert.shape)| ≤ cert.ε :=
  FiniteContinuousForgettingBridge.finiteMixture_abs_error_to_shifted_power_le
      (amplitude := cert.amplitude) (rateFn := cert.rateFn)
      (shape := cert.shape) (gammaRate := cert.gammaRate)
      (time := cert.time) (ε := cert.ε)
      cert.shape_pos cert.gammaRate_pos cert.time_nonneg
      cert.error_to_gamma

/-!
  Summary:
  - P199 turns P170's loose `hconv` / `hbound` obligations into named
    certificate objects.
  - Theorems then transport those certificates to shifted-power convergence or
    shifted-power bounded error by reusing P170/P147.

  Boundary:
  - This still does not prove that random sampled finite mixtures converge to a
    gamma distribution.  It states exactly what such a theorem, deterministic
    quadrature proof, or runtime harness must hand to Lean.
-/


end

end FiniteGammaBridgeCertificate
