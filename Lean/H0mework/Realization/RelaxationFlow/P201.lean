import H0mework.Realization.Relations.P199

/-!
# Proposition 201: error-envelope certificates for the finite→gamma bridge

P170 supplied the transport target: a finite exponential-rate mixture that
converges to the normalized gamma mixture also converges to the shifted-power
curve.  P199 named the convergence certificate object.  This file lowers that
obligation one more level: an explicit error envelope `εₙ → 0`, bounding the
finite mixture's error against the normalized gamma mixture at every
nonnegative time, constructs P199's convergence certificate.

This still is not a sampling theorem or an LLN.  It is the reusable certificate
shape a quadrature proof, empirical harness, or probabilistic theorem should
emit: finite mixture error is bounded by a shrinking envelope.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## A general real squeeze lemma for error envelopes -/

/-- If a real-valued approximation has absolute error bounded eventually by an
envelope that tends to zero, then it converges to the target. -/
theorem tendsto_of_eventually_abs_sub_le_error
    {Index : Type*} {l : Filter Index}
    {f error : Index → ℝ} {target : ℝ}
    (herror : Tendsto error l (𝓝 0))
    (hbound : ∀ᶠ n in l, |f n - target| ≤ error n) :
    Tendsto f l (𝓝 target) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds herror ?_ ?_
  · exact Eventually.of_forall fun n => dist_nonneg
  · filter_upwards [hbound] with n hn
    simpa [Real.dist_eq] using hn

/-! ## All-time error-envelope certificate -/

/-- A finite→gamma error-envelope certificate.

For every nonnegative time, the finite exponential-rate mixture differs from
the normalized gamma mixture by at most `error n`, and `error n → 0`.  This is
strictly stronger and more inspectable than P199's raw `Tendsto` field. -/
structure FiniteToGammaErrorEnvelopeCertificate
    (Index Agent : Type*) [Fintype Agent] (l : Filter Index) where
  amplitude : Index → Agent → ℝ
  rateFn : Index → Agent → ℝ
  shape : ℝ
  gammaRate : ℝ
  error : Index → ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  error_tendsto_zero : Tendsto error l (𝓝 0)
  error_to_gamma :
    ∀ {time : ℝ}, 0 ≤ time →
      ∀ᶠ n in l,
        |FiniteContinuousForgettingBridge.finiteExponentialRateMixture
            (amplitude n) (rateFn n) time -
          GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate time| ≤ error n

/-- THEOREM 1: an all-time shrinking error envelope generates P199's
finite→gamma convergence certificate. -/
def finiteToGammaConvergenceCertificate_of_errorEnvelope
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaErrorEnvelopeCertificate Index Agent l) :
    FiniteToGammaConvergenceCertificate Index Agent l where
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

/-- THEOREM 2: the same error-envelope certificate transports all the way to
shifted-power convergence by P199/P170/P147. -/
theorem finiteToGammaErrorEnvelope_tendsto_shiftedPower
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaErrorEnvelopeCertificate Index Agent l)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun n : Index =>
        FiniteContinuousForgettingBridge.finiteExponentialRateMixture
          (cert.amplitude n) (cert.rateFn n) time)
      l
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) :=
  finiteToGammaCertificate_tendsto_shiftedPower
    (finiteToGammaConvergenceCertificate_of_errorEnvelope cert) htime

/-- THEOREM 3: an all-time error-envelope certificate gives shifted-power
convergence at every point of any finite observation grid. -/
theorem finiteToGammaErrorEnvelope_grid_tendsto_shiftedPower
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaErrorEnvelopeCertificate Index Agent l)
    (grid : FiniteObservationGrid) :
    ∀ τ : grid.Time,
      Tendsto
        (fun n : Index =>
          FiniteContinuousForgettingBridge.finiteExponentialRateMixture
            (cert.amplitude n) (cert.rateFn n) (grid.time τ))
        l
        (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  intro τ
  exact finiteToGammaErrorEnvelope_tendsto_shiftedPower cert (grid.nonneg τ)

/-!
  Summary:
  - P201 makes P199's all-time convergence certificate constructible from a
    shrinking finite-mixture error envelope.
  - This is the certificate shape a deterministic quadrature theorem, LLN, or
    runtime empirical harness should produce before P170 transports the result
    to shifted-power forgetting.

  Boundary:
  - P201 does not prove that random sampled finite mixtures have such an
    envelope.  It proves that once the envelope exists and tends to zero, the
    finite→gamma→shifted-power bridge is machine-checkable end to end.
-/


end

end FiniteGammaBridgeCertificate
