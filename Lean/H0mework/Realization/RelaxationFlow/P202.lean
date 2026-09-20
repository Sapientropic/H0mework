import H0mework.Realization.RelaxationFlow.P201

/-!
# Proposition 202: finite-grid error envelopes for the finite→gamma bridge

P201 proves that an all-time shrinking error envelope constructs P199's
finite→gamma convergence certificate.  Real empirical harnesses more often own
a finite observation grid: a finite list of times, with an error envelope at
each time.  This file proves the grid-level bridge.

It deliberately remains a certificate theorem, not a sampling theorem:
probability / quadrature / runtime code must still produce the per-grid-time
shrinking envelopes.  Once they exist, Lean transports them to shifted-power
convergence on the whole finite grid.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Finite-grid shrinking-envelope certificate -/

/-- A finite observation-grid error-envelope certificate.

Unlike P201's all-time certificate, this only asks for a shrinking envelope at
the explicitly listed grid times.  The optional aggregate envelope uses the sum
of nonnegative grid errors, so a runtime harness can report one finite-grid
error budget without pretending to control all times. -/
structure FiniteGridToGammaErrorEnvelopeCertificate
    (Index Agent : Type*) [Fintype Agent] (l : Filter Index)
    (grid : FiniteObservationGrid) where
  decEq : DecidableEq grid.Time
  amplitude : Index → Agent → ℝ
  rateFn : Index → Agent → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : grid.Time → Index → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_nonneg : ∀ τ n, 0 ≤ error τ n
  error_tendsto_zero : ∀ τ : grid.Time, Tendsto (error τ) l (𝓝 0)
  error_to_gamma :
    ∀ τ : grid.Time,
      ∀ᶠ n in l,
        |FiniteContinuousForgettingBridge.finiteExponentialRateMixture
            (amplitude n) (rateFn n) (grid.time τ) -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate (grid.time τ)| ≤ error τ n

/-- Aggregate finite-grid error budget: sum the per-grid-time error envelopes.
-/
def finiteGridErrorSum
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    {grid : FiniteObservationGrid}
    (cert : FiniteGridToGammaErrorEnvelopeCertificate Index Agent l grid)
    (n : Index) : ℝ := by
  letI := cert.decEq
  exact ∑ τ : grid.Time, cert.error τ n

/-! ## Pointwise and aggregate convergence -/

/-- THEOREM 1: each finite-grid time has convergence to the normalized gamma
mixture. -/
theorem finiteGridErrorEnvelope_tendsto_gamma
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    {grid : FiniteObservationGrid}
    (cert : FiniteGridToGammaErrorEnvelopeCertificate Index Agent l grid)
    (τ : grid.Time) :
    Tendsto
      (fun n : Index =>
        FiniteContinuousForgettingBridge.finiteExponentialRateMixture
          (cert.amplitude n) (cert.rateFn n) (grid.time τ))
      l
      (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
        cert.shape cert.gammaRate (grid.time τ))) :=
  tendsto_of_eventually_abs_sub_le_error
    (cert.error_tendsto_zero τ) (cert.error_to_gamma τ)

/-- THEOREM 2: each finite-grid time transports to shifted-power convergence.
-/
theorem finiteGridErrorEnvelope_tendsto_shiftedPower
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    {grid : FiniteObservationGrid}
    (cert : FiniteGridToGammaErrorEnvelopeCertificate Index Agent l grid)
    (τ : grid.Time) :
    Tendsto
      (fun n : Index =>
        FiniteContinuousForgettingBridge.finiteExponentialRateMixture
          (cert.amplitude n) (cert.rateFn n) (grid.time τ))
      l
      (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) :=
  FiniteContinuousForgettingBridge.finiteMixture_tendsto_shifted_power_of_tendsto_gamma
    (amplitude := cert.amplitude) (rateFn := cert.rateFn)
    (shape := cert.shape) (gammaRate := cert.gammaRate)
    (time := grid.time τ)
    cert.shape_pos cert.gammaRate_pos (grid.nonneg τ)
    (finiteGridErrorEnvelope_tendsto_gamma cert τ)

/-- THEOREM 3: the aggregate finite-grid error budget tends to zero. -/
theorem finiteGridErrorSum_tendsto_zero
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    {grid : FiniteObservationGrid}
    (cert : FiniteGridToGammaErrorEnvelopeCertificate Index Agent l grid) :
    Tendsto (fun n : Index => finiteGridErrorSum cert n) l (𝓝 0) := by
  letI := cert.decEq
  unfold finiteGridErrorSum
  simpa using
    tendsto_finsetSum (Finset.univ : Finset grid.Time)
      (fun τ _ => cert.error_tendsto_zero τ)

/-- THEOREM 4: each pointwise gamma error is bounded by the aggregate
finite-grid error budget. -/
theorem finiteGrid_abs_error_le_errorSum
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    {grid : FiniteObservationGrid}
    (cert : FiniteGridToGammaErrorEnvelopeCertificate Index Agent l grid)
    (τ : grid.Time) :
    ∀ᶠ n in l,
      |FiniteContinuousForgettingBridge.finiteExponentialRateMixture
          (cert.amplitude n) (cert.rateFn n) (grid.time τ) -
        GammaMixtureForgetting.normalizedGammaLaplace
          cert.shape cert.gammaRate (grid.time τ)| ≤
        finiteGridErrorSum cert n := by
  letI := cert.decEq
  filter_upwards [cert.error_to_gamma τ] with n hn
  have hsingle :
      cert.error τ n ≤ finiteGridErrorSum cert n := by
    unfold finiteGridErrorSum
    simpa using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset grid.Time))
        (f := fun τ' : grid.Time => cert.error τ' n)
        (fun τ' _ => cert.error_nonneg τ' n)
        (Finset.mem_univ τ))
  exact hn.trans hsingle

/-- THEOREM 5: the aggregate finite-grid error budget is itself enough to
prove each finite-grid gamma convergence statement. -/
theorem finiteGridErrorEnvelope_tendsto_gamma_of_aggregate
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    {grid : FiniteObservationGrid}
    (cert : FiniteGridToGammaErrorEnvelopeCertificate Index Agent l grid)
    (τ : grid.Time) :
    Tendsto
      (fun n : Index =>
        FiniteContinuousForgettingBridge.finiteExponentialRateMixture
          (cert.amplitude n) (cert.rateFn n) (grid.time τ))
      l
      (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
        cert.shape cert.gammaRate (grid.time τ))) :=
  tendsto_of_eventually_abs_sub_le_error
    (finiteGridErrorSum_tendsto_zero cert)
    (finiteGrid_abs_error_le_errorSum cert τ)

/-!
  Summary:
  - P202 lowers the P201 bridge to the empirical finite-grid shape.
  - A harness may supply one shrinking error envelope per observation time.
  - Lean proves both pointwise shifted-power convergence and a single aggregate
    finite-grid error budget that also tends to zero.

  Boundary:
  - This still does not prove LLN, random order-statistics convergence, or
    concrete runtime mechanism-faithfulness.  It tells those producers exactly
    what finite-grid certificate shape will be accepted.
-/


end

end FiniteGammaBridgeCertificate
