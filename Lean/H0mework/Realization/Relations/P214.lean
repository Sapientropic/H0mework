import H0mework.Realization.Relations.P213

/-!
# Proposition 214: weighted Laplace producer certificates

P213 gives the variable-cardinality finite→gamma bridge in terms of generic
`amplitude` / `rateFn` arrays on `Fin N`.  Runtime harnesses and deterministic
quadrature code usually speak a slightly different language: finite weighted
rate nodes approximating the gamma Laplace functional.

This file supplies that producer-side adapter.  A weighted-node Laplace error
envelope, all-time or finite-grid, compiles into P213's variable-cardinality
finite-mixture envelope and therefore transports to shifted-power convergence.

Boundary: this still does not prove a particular quadrature rule or LLN.  It
turns the certificate such a producer emits into the P213 bridge object.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Weighted-node Laplace mixtures -/

/-- A finite weighted Laplace mixture at time `time`.

`weight N i` is the quadrature / empirical mass at rate node `node N i`.
-/
def variableWeightedLaplaceMixture
    (N : ℕ) (weight node : Fin N → ℝ) (time : ℝ) : ℝ :=
  variableFiniteExponentialRateMixture N weight node time

/-- A weighted-node all-time producer certificate.

For every nonnegative time, the finite weighted Laplace mixture converges to
the normalized gamma Laplace functional through a shrinking envelope.
-/
structure VariableWeightedLaplaceEnvelopeCertificate where
  weight : (N : ℕ) → Fin N → ℝ
  node : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : ℕ → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  laplace_error_to_gamma :
    ∀ {time : ℝ}, 0 ≤ time →
      ∀ᶠ N in atTop,
        |variableWeightedLaplaceMixture
            N (weight N) (node N) time -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate time| ≤ error N

/-- THEOREM 1: a weighted-node all-time producer certificate compiles to
P213's variable finite→gamma envelope certificate. -/
def VariableWeightedLaplaceEnvelopeCertificate.toVariableFiniteEnvelope
    (cert : VariableWeightedLaplaceEnvelopeCertificate) :
    VariableFiniteToGammaErrorEnvelopeCertificate where
  amplitude := cert.weight
  rateFn := cert.node
  shape := cert.shape
  gammaRate := cert.gammaRate
  error := cert.error
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  error_tendsto_zero := cert.error_tendsto_zero
  error_to_gamma := by
    intro time htime
    simpa [variableWeightedLaplaceMixture]
      using cert.laplace_error_to_gamma htime

/-- THEOREM 2: a weighted-node all-time producer certificate transports to
shifted-power convergence. -/
theorem variableWeightedLaplaceEnvelope_tendsto_shiftedPower
    (cert : VariableWeightedLaplaceEnvelopeCertificate)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun N : ℕ =>
        variableWeightedLaplaceMixture N (cert.weight N) (cert.node N) time)
      atTop
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [variableWeightedLaplaceMixture,
    VariableWeightedLaplaceEnvelopeCertificate.toVariableFiniteEnvelope] using
    variableFiniteErrorEnvelope_tendsto_shiftedPower
      cert.toVariableFiniteEnvelope htime

/-! ## Finite-grid max-error producer certificates -/

/-- A finite-grid weighted-node producer certificate with one max-error
envelope for the whole grid.

This is the common empirical shape: at each `N`, the harness reports one
finite-grid error budget controlling all listed observation times.
-/
structure VariableWeightedLaplaceGridMaxErrorCertificate
    (grid : FiniteObservationGrid) where
  decEq : DecidableEq grid.Time
  weight : (N : ℕ) → Fin N → ℝ
  node : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : ℕ → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_nonneg : ∀ N, 0 ≤ error N
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  grid_laplace_error_to_gamma :
    ∀ τ : grid.Time,
      ∀ᶠ N in atTop,
        |variableWeightedLaplaceMixture
            N (weight N) (node N) (grid.time τ) -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate (grid.time τ)| ≤ error N

/-- THEOREM 3: a finite-grid max-error weighted-node producer certificate
compiles to P213's finite-grid variable finite→gamma envelope certificate. -/
def VariableWeightedLaplaceGridMaxErrorCertificate.toVariableFiniteGridEnvelope
    {grid : FiniteObservationGrid}
    (cert : VariableWeightedLaplaceGridMaxErrorCertificate grid) :
    VariableFiniteGridToGammaErrorEnvelopeCertificate grid where
  decEq := cert.decEq
  amplitude := cert.weight
  rateFn := cert.node
  shape := cert.shape
  gammaRate := cert.gammaRate
  error := fun _ N => cert.error N
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  error_nonneg := by
    intro _ N
    exact cert.error_nonneg N
  error_tendsto_zero := by
    intro _
    exact cert.error_tendsto_zero
  error_to_gamma := by
    intro τ
    simpa [variableWeightedLaplaceMixture]
      using cert.grid_laplace_error_to_gamma τ

/-- THEOREM 4: every grid time transports to shifted-power convergence. -/
theorem variableWeightedLaplaceGridMaxError_tendsto_shiftedPower
    {grid : FiniteObservationGrid}
    (cert : VariableWeightedLaplaceGridMaxErrorCertificate grid)
    (τ : grid.Time) :
    Tendsto
      (fun N : ℕ =>
        variableWeightedLaplaceMixture
          N (cert.weight N) (cert.node N) (grid.time τ))
      atTop
      (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [variableWeightedLaplaceMixture,
    VariableWeightedLaplaceGridMaxErrorCertificate.toVariableFiniteGridEnvelope] using
    variableFiniteGridErrorEnvelope_tendsto_shiftedPower
      cert.toVariableFiniteGridEnvelope τ

/-- THEOREM 5: the compiled finite-grid aggregate budget tends to zero. -/
theorem variableWeightedLaplaceGridMaxError_sum_tendsto_zero
    {grid : FiniteObservationGrid}
    (cert : VariableWeightedLaplaceGridMaxErrorCertificate grid) :
    Tendsto
      (fun N : ℕ =>
        variableFiniteGridErrorSum cert.toVariableFiniteGridEnvelope N)
      atTop
      (𝓝 0) :=
  variableFiniteGridErrorSum_tendsto_zero cert.toVariableFiniteGridEnvelope

/-!
  Summary:
  - P214 converts the natural weighted-node Laplace approximation language
    into P213's variable-cardinality finite-mixture bridge certificate.
  - A single finite-grid max-error envelope is enough to feed the per-grid
    envelope bridge and therefore shifted-power convergence.

  Still outside this theorem:
  - proving a concrete quadrature / sampling method satisfies the envelope;
  - parameter estimation;
  - runtime mechanism-faithfulness.
-/


end

end FiniteGammaBridgeCertificate
