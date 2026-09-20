import H0mework.Realization.Relations.P216

/-!
# Proposition 217: empirical finite-grid residual certificates

P216 specializes the finite→gamma bridge to equal-weight empirical samples, but
it still asks a producer to supply a grid max-error envelope.  A runtime harness
usually owns an even more concrete object: the actual residual at each finite
observation time, plus an aggregate residual budget.

This file formalizes that object.  If the aggregate finite-grid gamma residual
of an equal-weight empirical sample tends to zero, it compiles into P216's
empirical grid max-error certificate and therefore transports to shifted-power
convergence.

Boundary: this is still not an LLN/order-statistics/quadrature theorem.  It is
the Lean-readable bridge from a concrete finite-grid residual report to the
already-certified shifted-power target.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Concrete finite-grid residuals -/

/-- The absolute residual of an equal-weight empirical Laplace mixture against
the normalized gamma Laplace target at one finite-grid observation time. -/
def empiricalEqualWeightGammaResidual
    {grid : FiniteObservationGrid}
    (sampleRate : (N : ℕ) → Fin N → ℝ)
    (shape gammaRate : ℝ) (N : ℕ) (τ : grid.Time) : ℝ :=
  |empiricalEqualWeightLaplaceMixture
      N (sampleRate N) (grid.time τ) -
    GammaMixtureForgetting.normalizedGammaLaplace
      shape gammaRate (grid.time τ)|

/-- Aggregate finite-grid residual budget: sum the actual absolute residuals
over the finite observation grid. -/
def empiricalEqualWeightGammaResidualSum
    {grid : FiniteObservationGrid}
    (sampleRate : (N : ℕ) → Fin N → ℝ)
    (shape gammaRate : ℝ) (N : ℕ) : ℝ :=
  ∑ τ : grid.Time,
    empiricalEqualWeightGammaResidual
      sampleRate shape gammaRate N τ

/-- THEOREM 1: each concrete residual is nonnegative. -/
theorem empiricalEqualWeightGammaResidual_nonneg
    {grid : FiniteObservationGrid}
    (sampleRate : (N : ℕ) → Fin N → ℝ)
    (shape gammaRate : ℝ) (N : ℕ) (τ : grid.Time) :
    0 ≤ empiricalEqualWeightGammaResidual
      sampleRate shape gammaRate N τ := by
  unfold empiricalEqualWeightGammaResidual
  exact abs_nonneg _

/-- THEOREM 2: the aggregate finite-grid residual budget is nonnegative. -/
theorem empiricalEqualWeightGammaResidualSum_nonneg
    {grid : FiniteObservationGrid}
    (sampleRate : (N : ℕ) → Fin N → ℝ)
    (shape gammaRate : ℝ) (N : ℕ) :
    0 ≤ empiricalEqualWeightGammaResidualSum
      (grid := grid) sampleRate shape gammaRate N := by
  unfold empiricalEqualWeightGammaResidualSum
  exact Finset.sum_nonneg fun τ _ =>
    empiricalEqualWeightGammaResidual_nonneg
      sampleRate shape gammaRate N τ

/-- THEOREM 3: each pointwise residual is bounded by the aggregate residual
budget. -/
theorem empiricalEqualWeightGammaResidual_le_residualSum
    {grid : FiniteObservationGrid} (_decEq : DecidableEq grid.Time)
    (sampleRate : (N : ℕ) → Fin N → ℝ)
    (shape gammaRate : ℝ) (N : ℕ) (τ : grid.Time) :
      empiricalEqualWeightGammaResidual
        sampleRate shape gammaRate N τ ≤
      empiricalEqualWeightGammaResidualSum
        (grid := grid) sampleRate shape gammaRate N := by
  letI := _decEq
  unfold empiricalEqualWeightGammaResidualSum
  exact
    (Finset.single_le_sum
      (s := (Finset.univ : Finset grid.Time))
      (f := fun τ' : grid.Time =>
        empiricalEqualWeightGammaResidual
          sampleRate shape gammaRate N τ')
      (fun τ' _ =>
        empiricalEqualWeightGammaResidual_nonneg
          sampleRate shape gammaRate N τ')
      (Finset.mem_univ τ))

/-! ## Residual-sum certificates compile to P216 -/

/-- A concrete finite-grid empirical residual certificate.

The only asymptotic producer obligation is that the actual aggregate residual
over the finite observation grid tends to zero.
-/
structure EmpiricalEqualWeightLaplaceGridResidualCertificate
    (grid : FiniteObservationGrid) where
  decEq : DecidableEq grid.Time
  sampleRate : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  residualSum_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        empiricalEqualWeightGammaResidualSum
          (grid := grid) sampleRate
          shape gammaRate N)
      atTop
      (𝓝 0)

/-- THEOREM 4: a concrete finite-grid residual certificate compiles to P216's
equal-weight empirical grid max-error certificate. -/
def EmpiricalEqualWeightLaplaceGridResidualCertificate.toGridMaxError
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridResidualCertificate grid) :
    EmpiricalEqualWeightLaplaceGridMaxErrorCertificate grid where
  decEq := cert.decEq
  sampleRate := cert.sampleRate
  shape := cert.shape
  gammaRate := cert.gammaRate
  error := fun N =>
    empiricalEqualWeightGammaResidualSum
      (grid := grid) cert.sampleRate
      cert.shape cert.gammaRate N
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  error_nonneg := by
    intro N
    exact empiricalEqualWeightGammaResidualSum_nonneg
      (grid := grid) cert.sampleRate cert.shape cert.gammaRate N
  error_tendsto_zero := by
    exact cert.residualSum_tendsto_zero
  grid_empirical_error_to_gamma := by
    intro τ
    exact Eventually.of_forall fun N =>
      empiricalEqualWeightGammaResidual_le_residualSum
        (grid := grid) cert.decEq cert.sampleRate cert.shape cert.gammaRate N τ

/-- THEOREM 5: a concrete finite-grid residual certificate transports every
grid time to shifted-power convergence. -/
theorem empiricalEqualWeightLaplaceGridResidual_tendsto_shiftedPower
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridResidualCertificate grid)
    (τ : grid.Time) :
    Tendsto
      (fun N : ℕ =>
        empiricalEqualWeightLaplaceMixture
          N (cert.sampleRate N) (grid.time τ))
      atTop
      (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [EmpiricalEqualWeightLaplaceGridResidualCertificate.toGridMaxError]
    using
      empiricalEqualWeightLaplaceGridMaxError_tendsto_shiftedPower
        cert.toGridMaxError τ

/-- THEOREM 6: the compiled P213/P214/P216 aggregate budget tends to zero. -/
theorem empiricalEqualWeightLaplaceGridResidual_compiled_sum_tendsto_zero
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridResidualCertificate grid) :
    Tendsto
      (fun N : ℕ =>
        variableFiniteGridErrorSum
          cert.toGridMaxError.toWeightedGridMaxError.toVariableFiniteGridEnvelope N)
      atTop
      (𝓝 0) :=
  empiricalEqualWeightLaplaceGridMaxError_sum_tendsto_zero
    cert.toGridMaxError

/-!
  Summary:
  - P217 lowers the P216 grid certificate to concrete residual reports.
  - The residual sum is nonnegative and pointwise-dominates every grid residual.
  - Once that residual sum tends to zero, the existing P216/P214/P213 bridge
    transports the empirical finite-grid approximation to shifted-power.

  Still outside this theorem:
  - proving why a sampling/quadrature/runtime process makes the residual sum
    tend to zero;
  - all-time (off-grid) convergence;
  - empirical parameter estimation.
-/


end

end FiniteGammaBridgeCertificate
