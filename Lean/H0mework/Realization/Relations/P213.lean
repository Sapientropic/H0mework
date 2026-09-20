import H0mework.Realization.RelaxationFlow.P202

/-!
# Proposition 213: variable-cardinality finite→gamma bridge certificates

P170 gave the reusable transport target: once a finite exponential-rate
mixture is known to converge to the normalized gamma mixture, P147 transports
the result to the shifted-power curve.  P199-P202 named several certificate
forms, but those certificates keep a fixed finite `Agent` type.

This file closes the more literal finite-to-continuous bridge shape: the `N`th
approximation may use `Fin N` mixture atoms.  A shrinking error envelope for
those variable-cardinality mixtures generates convergence to the continuous
gamma mixture, and therefore to shifted-power forgetting.

Boundary: this is still not an LLN/order-statistics/quadrature theorem.  It is
the Lean-readable producer-side certificate shape such theorems or empirical
harnesses should emit.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Variable-cardinality mixtures -/

/-- A finite exponential-rate mixture whose carrier is `Fin N`.

Unlike P170's fixed-`Agent` mixture, this is the shape needed for a genuine
finite-to-continuous approximation sequence: as `N → ∞`, the number of mixture
atoms may grow.
-/
def variableFiniteExponentialRateMixture
    (N : ℕ) (amplitude rateFn : Fin N → ℝ) (time : ℝ) : ℝ :=
  FiniteContinuousForgettingBridge.finiteExponentialRateMixture
    amplitude rateFn time

/-- A direct variable-cardinality convergence certificate.

It says that the sequence of `Fin N` finite mixtures converges pointwise, for
every nonnegative time, to the normalized gamma mixture.
-/
structure VariableFiniteToGammaConvergenceCertificate where
  amplitude : (N : ℕ) → Fin N → ℝ
  rateFn : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  finite_tendsto_gamma :
    ∀ {time : ℝ}, 0 ≤ time →
      Tendsto
        (fun N : ℕ =>
          variableFiniteExponentialRateMixture
            N (amplitude N) (rateFn N) time)
        atTop
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate time))

/-- THEOREM 1: a variable-cardinality finite→gamma convergence certificate
transports to shifted-power convergence. -/
theorem variableFiniteToGammaCertificate_tendsto_shiftedPower
    (cert : VariableFiniteToGammaConvergenceCertificate)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun N : ℕ =>
        variableFiniteExponentialRateMixture
          N (cert.amplitude N) (cert.rateFn N) time)
      atTop
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [variableFiniteExponentialRateMixture,
    GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
      cert.shape_pos cert.gammaRate_pos htime]
    using cert.finite_tendsto_gamma htime

/-! ## Shrinking error envelopes generate the convergence certificate -/

/-- A producer-side variable-cardinality error-envelope certificate.

For every nonnegative time, the `Fin N` finite mixture differs from the
normalized gamma mixture by at most `error N` eventually, and `error N → 0`.
This is the concrete reusable bridge certificate P170 was missing.
-/
structure VariableFiniteToGammaErrorEnvelopeCertificate where
  amplitude : (N : ℕ) → Fin N → ℝ
  rateFn : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : ℕ → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  error_to_gamma :
    ∀ {time : ℝ}, 0 ≤ time →
      ∀ᶠ N in atTop,
        |variableFiniteExponentialRateMixture
            N (amplitude N) (rateFn N) time -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate time| ≤ error N

/-- THEOREM 2: a variable-cardinality shrinking envelope generates the direct
variable-cardinality finite→gamma convergence certificate. -/
def variableFiniteToGammaConvergenceCertificate_of_errorEnvelope
    (cert : VariableFiniteToGammaErrorEnvelopeCertificate) :
    VariableFiniteToGammaConvergenceCertificate where
  amplitude := cert.amplitude
  rateFn := cert.rateFn
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  finite_tendsto_gamma := by
    intro time htime
    exact tendsto_of_eventually_abs_sub_le_error
      cert.error_tendsto_zero (cert.error_to_gamma htime)

/-- THEOREM 3: a variable-cardinality shrinking envelope transports all the
way to shifted-power convergence. -/
theorem variableFiniteErrorEnvelope_tendsto_shiftedPower
    (cert : VariableFiniteToGammaErrorEnvelopeCertificate)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun N : ℕ =>
        variableFiniteExponentialRateMixture
          N (cert.amplitude N) (cert.rateFn N) time)
      atTop
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) :=
  variableFiniteToGammaCertificate_tendsto_shiftedPower
    (variableFiniteToGammaConvergenceCertificate_of_errorEnvelope cert) htime

/-! ## Finite observation grids with variable cardinality -/

/-- Finite-grid version of the variable-cardinality envelope.

This is the form closest to empirical harness output: for every listed
observation time, the `Fin N` mixture has a shrinking envelope against the
continuous gamma target.
-/
structure VariableFiniteGridToGammaErrorEnvelopeCertificate
    (grid : FiniteObservationGrid) where
  decEq : DecidableEq grid.Time
  amplitude : (N : ℕ) → Fin N → ℝ
  rateFn : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : grid.Time → ℕ → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_nonneg : ∀ τ N, 0 ≤ error τ N
  error_tendsto_zero : ∀ τ : grid.Time, Tendsto (error τ) atTop (𝓝 0)
  error_to_gamma :
    ∀ τ : grid.Time,
      ∀ᶠ N in atTop,
        |variableFiniteExponentialRateMixture
            N (amplitude N) (rateFn N) (grid.time τ) -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate (grid.time τ)| ≤ error τ N

/-- Aggregate finite-grid error budget for the variable-cardinality bridge. -/
def variableFiniteGridErrorSum
    {grid : FiniteObservationGrid}
    (cert : VariableFiniteGridToGammaErrorEnvelopeCertificate grid)
    (N : ℕ) : ℝ := by
  letI := cert.decEq
  exact ∑ τ : grid.Time, cert.error τ N

/-- THEOREM 4: each finite-grid time has convergence to the normalized gamma
mixture. -/
theorem variableFiniteGridErrorEnvelope_tendsto_gamma
    {grid : FiniteObservationGrid}
    (cert : VariableFiniteGridToGammaErrorEnvelopeCertificate grid)
    (τ : grid.Time) :
    Tendsto
      (fun N : ℕ =>
        variableFiniteExponentialRateMixture
          N (cert.amplitude N) (cert.rateFn N) (grid.time τ))
      atTop
      (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
        cert.shape cert.gammaRate (grid.time τ))) :=
  tendsto_of_eventually_abs_sub_le_error
    (cert.error_tendsto_zero τ) (cert.error_to_gamma τ)

/-- THEOREM 5: each finite-grid time transports to shifted-power convergence.
-/
theorem variableFiniteGridErrorEnvelope_tendsto_shiftedPower
    {grid : FiniteObservationGrid}
    (cert : VariableFiniteGridToGammaErrorEnvelopeCertificate grid)
    (τ : grid.Time) :
    Tendsto
      (fun N : ℕ =>
        variableFiniteExponentialRateMixture
          N (cert.amplitude N) (cert.rateFn N) (grid.time τ))
      atTop
      (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
      cert.shape_pos cert.gammaRate_pos (grid.nonneg τ)]
    using variableFiniteGridErrorEnvelope_tendsto_gamma cert τ

/-- THEOREM 6: the aggregate finite-grid error budget tends to zero. -/
theorem variableFiniteGridErrorSum_tendsto_zero
    {grid : FiniteObservationGrid}
    (cert : VariableFiniteGridToGammaErrorEnvelopeCertificate grid) :
    Tendsto (fun N : ℕ => variableFiniteGridErrorSum cert N) atTop (𝓝 0) := by
  letI := cert.decEq
  unfold variableFiniteGridErrorSum
  simpa using
    tendsto_finsetSum (Finset.univ : Finset grid.Time)
      (fun τ _ => cert.error_tendsto_zero τ)

/-- THEOREM 7: each pointwise gamma error is bounded by the aggregate
finite-grid error budget. -/
theorem variableFiniteGrid_abs_error_le_errorSum
    {grid : FiniteObservationGrid}
    (cert : VariableFiniteGridToGammaErrorEnvelopeCertificate grid)
    (τ : grid.Time) :
    ∀ᶠ N in atTop,
      |variableFiniteExponentialRateMixture
          N (cert.amplitude N) (cert.rateFn N) (grid.time τ) -
        GammaMixtureForgetting.normalizedGammaLaplace
          cert.shape cert.gammaRate (grid.time τ)| ≤
        variableFiniteGridErrorSum cert N := by
  letI := cert.decEq
  filter_upwards [cert.error_to_gamma τ] with N hn
  have hsingle :
      cert.error τ N ≤ variableFiniteGridErrorSum cert N := by
    unfold variableFiniteGridErrorSum
    simpa using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset grid.Time))
        (f := fun τ' : grid.Time => cert.error τ' N)
        (fun τ' _ => cert.error_nonneg τ' N)
        (Finset.mem_univ τ))
  exact hn.trans hsingle

/-!
  Summary:
  - P213 is the producer-side bridge certificate missing from the P170 story.
  - It supports genuinely growing finite mixtures (`Fin N`) rather than only a
    fixed finite carrier.
  - A shrinking error envelope against normalized gamma now produces
    convergence to normalized gamma and shifted-power, all-time or finite-grid.

  Still outside this theorem:
  - deriving the envelope from LLN, deterministic quadrature, or order
    statistics;
  - empirical parameter estimation;
  - runtime mechanism-faithfulness.
-/


end

end FiniteGammaBridgeCertificate
