import H0mework.Realization.Relations.P214

/-!
# Proposition 216: empirical equal-weight Laplace producer certificates

P213/P214 made the finite→gamma bridge certificate-shaped, and P214 added a
weighted-node Laplace adapter.  The most common empirical / LLN producer shape
is still narrower: the `N`th approximation is an equal-weight empirical mean
over `N` sampled rate nodes.

This file formalizes that producer shape.  It does not prove an LLN, random
order-statistics theorem, or a deterministic quadrature rule.  It proves that
an equal-weight empirical Laplace envelope is a concrete instance of P214's
weighted-node envelope, and therefore transports to shifted-power convergence.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Equal-weight empirical Laplace mixtures -/

/-- Equal empirical weight for a carrier of size `N`.

For `N = 0` the carrier `Fin N` is empty, so the value is never consumed by a
summand.  This keeps the sequence total on `ℕ`; all convergence statements are
eventual at `atTop`, so the empty zeroth approximation carries no asymptotic
content.
-/
def empiricalEqualWeight (N : ℕ) (_ : Fin N) : ℝ :=
  (N : ℝ)⁻¹

/-- The equal-weight empirical Laplace mixture at time `time`. -/
def empiricalEqualWeightLaplaceMixture
    (N : ℕ) (sampleRate : Fin N → ℝ) (time : ℝ) : ℝ :=
  variableWeightedLaplaceMixture
    N (empiricalEqualWeight N) sampleRate time

/-- THEOREM 1: equal empirical weights are nonnegative. -/
theorem empiricalEqualWeight_nonneg
    (N : ℕ) (i : Fin N) :
    0 ≤ empiricalEqualWeight N i := by
  unfold empiricalEqualWeight
  exact inv_nonneg.mpr (Nat.cast_nonneg N)

/-- THEOREM 2: for a nonempty empirical carrier, equal weights sum to one. -/
theorem empiricalEqualWeight_sum_eq_one
    {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin N, empiricalEqualWeight N i) = 1 := by
  unfold empiricalEqualWeight
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  field_simp [hNne]

/-! ## All-time empirical producer certificates -/

/-- All-time equal-weight empirical producer certificate.

The certificate says that the empirical mean of sampled exponential rates
approximates the normalized gamma Laplace functional with a shrinking envelope.
This is the exact theorem-shaped obligation an LLN or empirical harness should
emit for the all-time route.
-/
structure EmpiricalEqualWeightLaplaceEnvelopeCertificate where
  sampleRate : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : ℕ → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  empirical_error_to_gamma :
    ∀ {time : ℝ}, 0 ≤ time →
      ∀ᶠ N in atTop,
        |empiricalEqualWeightLaplaceMixture
            N (sampleRate N) time -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate time| ≤ error N

/-- THEOREM 3: an equal-weight empirical all-time producer certificate compiles
to P214's weighted-node producer certificate. -/
def EmpiricalEqualWeightLaplaceEnvelopeCertificate.toWeightedLaplaceEnvelope
    (cert : EmpiricalEqualWeightLaplaceEnvelopeCertificate) :
    VariableWeightedLaplaceEnvelopeCertificate where
  weight := fun N => empiricalEqualWeight N
  node := cert.sampleRate
  shape := cert.shape
  gammaRate := cert.gammaRate
  error := cert.error
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  error_tendsto_zero := cert.error_tendsto_zero
  laplace_error_to_gamma := by
    intro time htime
    simpa [empiricalEqualWeightLaplaceMixture]
      using cert.empirical_error_to_gamma htime

/-- THEOREM 4: an equal-weight empirical all-time producer certificate
transports to shifted-power convergence. -/
theorem empiricalEqualWeightLaplaceEnvelope_tendsto_shiftedPower
    (cert : EmpiricalEqualWeightLaplaceEnvelopeCertificate)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun N : ℕ =>
        empiricalEqualWeightLaplaceMixture
          N (cert.sampleRate N) time)
      atTop
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [empiricalEqualWeightLaplaceMixture,
    EmpiricalEqualWeightLaplaceEnvelopeCertificate.toWeightedLaplaceEnvelope]
    using
      variableWeightedLaplaceEnvelope_tendsto_shiftedPower
        cert.toWeightedLaplaceEnvelope htime

/-! ## Finite-grid empirical producer certificates -/

/-- Finite-grid equal-weight empirical producer certificate with one max-error
envelope for the whole grid.

This is the shape closest to a finite experimental or runtime report: for each
sample size `N`, one max error controls every listed observation time.
-/
structure EmpiricalEqualWeightLaplaceGridMaxErrorCertificate
    (grid : FiniteObservationGrid) where
  decEq : DecidableEq grid.Time
  sampleRate : (N : ℕ) → Fin N → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : ℕ → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_nonneg : ∀ N, 0 ≤ error N
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  grid_empirical_error_to_gamma :
    ∀ τ : grid.Time,
      ∀ᶠ N in atTop,
        |empiricalEqualWeightLaplaceMixture
            N (sampleRate N) (grid.time τ) -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate (grid.time τ)| ≤ error N

/-- THEOREM 5: a finite-grid equal-weight empirical certificate compiles to
P214's finite-grid weighted-node certificate. -/
def EmpiricalEqualWeightLaplaceGridMaxErrorCertificate.toWeightedGridMaxError
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridMaxErrorCertificate grid) :
    VariableWeightedLaplaceGridMaxErrorCertificate grid where
  decEq := cert.decEq
  weight := fun N => empiricalEqualWeight N
  node := cert.sampleRate
  shape := cert.shape
  gammaRate := cert.gammaRate
  error := cert.error
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  error_nonneg := cert.error_nonneg
  error_tendsto_zero := cert.error_tendsto_zero
  grid_laplace_error_to_gamma := by
    intro τ
    simpa [empiricalEqualWeightLaplaceMixture]
      using cert.grid_empirical_error_to_gamma τ

/-- THEOREM 6: every grid time transports to shifted-power convergence. -/
theorem empiricalEqualWeightLaplaceGridMaxError_tendsto_shiftedPower
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridMaxErrorCertificate grid)
    (τ : grid.Time) :
    Tendsto
      (fun N : ℕ =>
        empiricalEqualWeightLaplaceMixture
          N (cert.sampleRate N) (grid.time τ))
      atTop
      (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [empiricalEqualWeightLaplaceMixture,
    EmpiricalEqualWeightLaplaceGridMaxErrorCertificate.toWeightedGridMaxError]
    using
      variableWeightedLaplaceGridMaxError_tendsto_shiftedPower
        cert.toWeightedGridMaxError τ

/-- THEOREM 7: the compiled P213/P214 finite-grid aggregate budget tends to
zero. -/
theorem empiricalEqualWeightLaplaceGridMaxError_sum_tendsto_zero
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridMaxErrorCertificate grid) :
    Tendsto
      (fun N : ℕ =>
        variableFiniteGridErrorSum
          cert.toWeightedGridMaxError.toVariableFiniteGridEnvelope N)
      atTop
      (𝓝 0) :=
  variableWeightedLaplaceGridMaxError_sum_tendsto_zero
    cert.toWeightedGridMaxError

/-!
  Summary:
  - P216 specializes P214's weighted-node producer language to the empirical
    equal-weight mean shape.
  - Equal weights are proved nonnegative and sum to one on every nonempty
    carrier.
  - All-time and finite-grid empirical envelopes compile to P214/P213 and
    therefore transport to shifted-power convergence.

  Still outside this theorem:
  - proving that random samples from a gamma rate distribution satisfy the
    envelope;
  - deterministic quadrature construction of the envelope;
  - empirical parameter estimation or runtime mechanism-faithfulness.
-/


end

end FiniteGammaBridgeCertificate
