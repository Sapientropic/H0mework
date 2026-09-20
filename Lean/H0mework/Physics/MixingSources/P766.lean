import H0mework.Physics.MixingSources.P765

/-!
# Proposition 766: CKM matrix phase uniquely locks running sigma

P765 closes the forward chain:

`CKM matrix depth 386 * sigmaGUTTwoLoopExact = raw phase 5.126`.

This file proves the producer direction.  The matrix-level phase equation has
one rational solution, and that solution is exactly `2563/193000`.  Therefore
the exact running sigma is not an extra free input once the CKM matrix depth
and raw phase target are fixed.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-- The matrix-level CKM phase equation for a candidate running sigma. -/
def CKMMatrixRunningSigmaSolution (σ : ℚ) : Prop :=
  (ckmJarlskogDepthFromMatrix : ℚ) * σ = cpRawPhaseClaim ℚ

/-- The matrix-level Jarlskog depth read as a rational is exactly `386`. -/
theorem ckmJarlskogDepthFromMatrix_rat_eq_386 :
    (ckmJarlskogDepthFromMatrix : ℚ) = (386 : ℚ) := by
  calc
    (ckmJarlskogDepthFromMatrix : ℚ) = (ckmCPDepthSum : ℚ) := by
      exact_mod_cast ckmJarlskogDepthFromMatrix_eq_386
    _ = (386 : ℚ) := by
      norm_num [ckmCPDepthSum]

/-- THEOREM 1: the CKM matrix phase equation uniquely selects the exact
running sigma `2563/193000`. -/
theorem ckmMatrixRunningSigmaSolution_iff_exact (σ : ℚ) :
    CKMMatrixRunningSigmaSolution σ ↔
      σ = sigmaGUTTwoLoopExact ℚ := by
  constructor
  · intro h
    unfold CKMMatrixRunningSigmaSolution at h
    rw [ckmJarlskogDepthFromMatrix_rat_eq_386] at h
    norm_num [cpRawPhaseClaim] at h
    norm_num [sigmaGUTTwoLoopExact]
    linarith
  · intro h
    rw [h]
    exact ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim

/-- THEOREM 2: the exact running sigma solves the CKM matrix phase equation. -/
theorem sigmaGUTTwoLoopExact_solves_ckmMatrixPhase :
    CKMMatrixRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ) :=
  (ckmMatrixRunningSigmaSolution_iff_exact
    (sigmaGUTTwoLoopExact ℚ)).mpr rfl

/-- THEOREM 3: nominal `13/1000` is not the exact matrix-phase solution. -/
theorem sigmaGUTNominal_not_ckmMatrixPhase_solution :
    ¬ CKMMatrixRunningSigmaSolution (sigmaGUTNominal ℚ) := by
  intro h
  have hsigma :=
    (ckmMatrixRunningSigmaSolution_iff_exact
      (sigmaGUTNominal ℚ)).mp h
  norm_num [sigmaGUTNominal, sigmaGUTTwoLoopExact] at hsigma

/-- THEOREM 4: rounded decimal proxy `0.01328 = 83/6250` is not the exact
matrix-phase solution. -/
theorem sigmaGUTTwoLoopDecimalProxy_not_ckmMatrixPhase_solution :
    ¬ CKMMatrixRunningSigmaSolution (sigmaGUTTwoLoopDecimalProxy ℚ) := by
  intro h
  have hsigma :=
    (ckmMatrixRunningSigmaSolution_iff_exact
      (sigmaGUTTwoLoopDecimalProxy ℚ)).mp h
  norm_num [sigmaGUTTwoLoopDecimalProxy, sigmaGUTTwoLoopExact] at hsigma

/-- The CKM phase-sigma producer certificate: the physicalized CKM phase
closure plus uniqueness of the running-sigma solution. -/
structure CKMRunningSigmaProducerCertificate : Prop where
  physicalized_ckm_phase :
    PhysicalizedCKMPhaseProducerCertificate
  solution_iff_exact :
    ∀ σ : ℚ,
      CKMMatrixRunningSigmaSolution σ ↔
        σ = sigmaGUTTwoLoopExact ℚ
  exact_solves :
    CKMMatrixRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ)
  nominal_rejected :
    ¬ CKMMatrixRunningSigmaSolution (sigmaGUTNominal ℚ)
  decimal_proxy_rejected :
    ¬ CKMMatrixRunningSigmaSolution (sigmaGUTTwoLoopDecimalProxy ℚ)
  exact_sigma_value :
    sigmaGUTTwoLoopExact ℚ = (2563 : ℚ) / 193000
  matrix_depth_value :
    (ckmJarlskogDepthFromMatrix : ℚ) = (386 : ℚ)
  raw_phase_value :
    cpRawPhaseClaim ℚ = (5126 : ℚ) / 1000

/-- THEOREM 5: canonical CKM running-sigma producer certificate. -/
theorem ckmRunningSigmaProducerCertificate :
    CKMRunningSigmaProducerCertificate where
  physicalized_ckm_phase :=
    physicalizedCKMPhaseProducerCertificate
  solution_iff_exact :=
    ckmMatrixRunningSigmaSolution_iff_exact
  exact_solves :=
    sigmaGUTTwoLoopExact_solves_ckmMatrixPhase
  nominal_rejected :=
    sigmaGUTNominal_not_ckmMatrixPhase_solution
  decimal_proxy_rejected :=
    sigmaGUTTwoLoopDecimalProxy_not_ckmMatrixPhase_solution
  exact_sigma_value := by
    norm_num [sigmaGUTTwoLoopExact]
  matrix_depth_value :=
    ckmJarlskogDepthFromMatrix_rat_eq_386
  raw_phase_value := by
    norm_num [cpRawPhaseClaim]

end StandardModelConstraint
end SaturationMonoid
