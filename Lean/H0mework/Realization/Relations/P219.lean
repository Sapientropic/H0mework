import H0mework.Realization.Relations.P217

/-!
# Proposition 219: canonical P170 bridge certificates

P170 is the reusable transport target: once a finite-mixture approximation is
known to converge to the normalized gamma Laplace functional, P147 identifies
that target with shifted-power forgetting.

P199/P201/P202/P213/P214/P216/P217 each expose a producer-facing certificate
shape, but the target still lacked one small facade: a canonical certificate
object whose only payload is "this finite mixture sequence converges to the
continuous gamma target".  This file adds that facade and proves the existing
producer certificates compile into it.

Boundary: this is still not an LLN, order-statistics theorem, deterministic
quadrature theorem, or runtime mechanism-faithfulness proof.  It closes the
certificate plumbing around P170, not the sampling theorem that might produce a
certificate.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Canonical all-time bridge certificate -/

/-- Canonical P170 bridge certificate.

The carrier and producer details are erased into one function
`mixture : Index -> time -> value`; the proof field says this finite-mixture
sequence converges pointwise to the continuous normalized gamma mixture for
every nonnegative time.
-/
structure CanonicalFiniteGammaBridgeCertificate
    (Index : Type*) (l : Filter Index) where
  mixture : Index → ℝ → ℝ
  shape : ℝ
  gammaRate : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  tendsToGamma :
    ∀ {time : ℝ}, 0 ≤ time →
      Tendsto
        (fun n : Index => mixture n time)
        l
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate time))

/-- THEOREM 1: the canonical P170 bridge transports directly to the
shifted-power target. -/
theorem canonicalFiniteGammaBridge_tendsto_shiftedPower
    {Index : Type*} {l : Filter Index}
    (cert : CanonicalFiniteGammaBridgeCertificate Index l)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun n : Index => cert.mixture n time)
      l
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
      cert.shape_pos cert.gammaRate_pos htime]
    using cert.tendsToGamma htime

/-- THEOREM 2: P199's fixed-carrier finite→gamma certificate compiles into the
canonical P170 bridge certificate. -/
def CanonicalFiniteGammaBridgeCertificate.ofFixedCarrier
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaConvergenceCertificate Index Agent l) :
    CanonicalFiniteGammaBridgeCertificate Index l where
  mixture := fun n time =>
    FiniteContinuousForgettingBridge.finiteExponentialRateMixture
      (cert.amplitude n) (cert.rateFn n) time
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  tendsToGamma := by
    intro time htime
    exact cert.finite_tendsto_gamma htime

/-- THEOREM 3: a P201 shrinking-envelope certificate compiles into the
canonical P170 bridge certificate. -/
def CanonicalFiniteGammaBridgeCertificate.ofFixedCarrierErrorEnvelope
    {Index Agent : Type*} [Fintype Agent] {l : Filter Index}
    (cert : FiniteToGammaErrorEnvelopeCertificate Index Agent l) :
    CanonicalFiniteGammaBridgeCertificate Index l :=
  CanonicalFiniteGammaBridgeCertificate.ofFixedCarrier
    (finiteToGammaConvergenceCertificate_of_errorEnvelope cert)

/-- THEOREM 4: P213's genuinely growing `Fin N` finite→gamma certificate
compiles into the canonical P170 bridge certificate. -/
def CanonicalFiniteGammaBridgeCertificate.ofVariableCardinality
    (cert : VariableFiniteToGammaConvergenceCertificate) :
    CanonicalFiniteGammaBridgeCertificate ℕ atTop where
  mixture := fun N time =>
    variableFiniteExponentialRateMixture
      N (cert.amplitude N) (cert.rateFn N) time
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  tendsToGamma := by
    intro time htime
    exact cert.finite_tendsto_gamma htime

/-- THEOREM 5: P213's growing-carrier shrinking-envelope certificate compiles
into the canonical P170 bridge certificate. -/
def CanonicalFiniteGammaBridgeCertificate.ofVariableErrorEnvelope
    (cert : VariableFiniteToGammaErrorEnvelopeCertificate) :
    CanonicalFiniteGammaBridgeCertificate ℕ atTop :=
  CanonicalFiniteGammaBridgeCertificate.ofVariableCardinality
    (variableFiniteToGammaConvergenceCertificate_of_errorEnvelope cert)

/-- THEOREM 6: P216's equal-weight empirical all-time envelope compiles into
the canonical P170 bridge certificate. -/
def CanonicalFiniteGammaBridgeCertificate.ofEmpiricalEqualWeightEnvelope
    (cert : EmpiricalEqualWeightLaplaceEnvelopeCertificate) :
    CanonicalFiniteGammaBridgeCertificate ℕ atTop where
  mixture := fun N time =>
    empiricalEqualWeightLaplaceMixture N (cert.sampleRate N) time
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  tendsToGamma := by
    intro time htime
    exact tendsto_of_eventually_abs_sub_le_error
      cert.error_tendsto_zero (cert.empirical_error_to_gamma htime)

/-! ## Canonical finite-grid bridge certificate -/

/-- Canonical finite-grid P170 bridge certificate.

This is the grid-level version owned by empirical/runtime reports: convergence
is only claimed at the finite list of observation times.
-/
structure CanonicalFiniteGridGammaBridgeCertificate
    (grid : FiniteObservationGrid) where
  mixture : ℕ → grid.Time → ℝ
  shape : ℝ
  gammaRate : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  tendsToGamma :
    ∀ τ : grid.Time,
      Tendsto
        (fun N : ℕ => mixture N τ)
        atTop
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (grid.time τ)))

/-- THEOREM 7: the canonical finite-grid bridge transports each listed time
to shifted-power convergence. -/
theorem canonicalFiniteGridGammaBridge_tendsto_shiftedPower
    {grid : FiniteObservationGrid}
    (cert : CanonicalFiniteGridGammaBridgeCertificate grid)
    (τ : grid.Time) :
    Tendsto
      (fun N : ℕ => cert.mixture N τ)
      atTop
      (𝓝 ((1 + grid.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
      cert.shape_pos cert.gammaRate_pos (grid.nonneg τ)]
    using cert.tendsToGamma τ

/-- THEOREM 8: P213's variable-cardinality finite-grid envelope compiles into
the canonical finite-grid P170 bridge certificate. -/
def CanonicalFiniteGridGammaBridgeCertificate.ofVariableGridEnvelope
    {grid : FiniteObservationGrid}
    (cert : VariableFiniteGridToGammaErrorEnvelopeCertificate grid) :
    CanonicalFiniteGridGammaBridgeCertificate grid where
  mixture := fun N τ =>
    variableFiniteExponentialRateMixture
      N (cert.amplitude N) (cert.rateFn N) (grid.time τ)
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  tendsToGamma := by
    intro τ
    exact variableFiniteGridErrorEnvelope_tendsto_gamma cert τ

/-- THEOREM 9: P216's equal-weight empirical finite-grid max-error envelope
compiles into the canonical finite-grid P170 bridge certificate. -/
def CanonicalFiniteGridGammaBridgeCertificate.ofEmpiricalGridMaxError
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridMaxErrorCertificate grid) :
    CanonicalFiniteGridGammaBridgeCertificate grid where
  mixture := fun N τ =>
    empiricalEqualWeightLaplaceMixture
      N (cert.sampleRate N) (grid.time τ)
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  tendsToGamma := by
    intro τ
    exact tendsto_of_eventually_abs_sub_le_error
      cert.error_tendsto_zero (cert.grid_empirical_error_to_gamma τ)

/-- THEOREM 10: P217's concrete residual-sum certificate compiles into the
canonical finite-grid P170 bridge certificate. -/
def CanonicalFiniteGridGammaBridgeCertificate.ofEmpiricalGridResidual
    {grid : FiniteObservationGrid}
    (cert : EmpiricalEqualWeightLaplaceGridResidualCertificate grid) :
    CanonicalFiniteGridGammaBridgeCertificate grid where
  mixture := fun N τ =>
    empiricalEqualWeightLaplaceMixture
      N (cert.sampleRate N) (grid.time τ)
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  tendsToGamma := by
    intro τ
    exact tendsto_of_eventually_abs_sub_le_error
      cert.residualSum_tendsto_zero
      (Eventually.of_forall fun N => by
        simpa [empiricalEqualWeightGammaResidual]
          using empiricalEqualWeightGammaResidual_le_residualSum
            (grid := grid) cert.decEq cert.sampleRate
            cert.shape cert.gammaRate N τ)

/-!
  Summary:
  - P219 gives P170 a canonical certificate facade.
  - P199/P201 fixed-carrier certificates, P213 growing-`Fin N` certificates,
    P216 empirical envelopes, and P217 residual reports all compile into that
    facade.
  - The facade then transports to shifted-power by P147.

  Still outside this theorem:
  - LLN / random sampling convergence;
  - deterministic quadrature convergence;
  - empirical parameter estimation;
  - runtime mechanism-faithfulness.
-/


end

end FiniteGammaBridgeCertificate
