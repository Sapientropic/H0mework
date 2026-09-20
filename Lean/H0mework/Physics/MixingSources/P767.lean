import H0mework.Physics.MixingSources.P766

/-!
# Proposition 767: source-law CKM sigma producer

P766 proves that the CKM matrix phase equation uniquely locks the exact
running sigma.

This file pushes the same lock one step upstream.  The full-beta-vector
source-law axis from P678 already forces

`2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis = 386`.

Therefore the source-law axis itself carries the CKM phase equation:

`(2 * gap) * sigma = 5.126`.

The unique rational solution is again `sigmaGUTTwoLoopExact = 2563/193000`.
This removes the remaining presentation gap between the physical source-law
axis and the matrix-level CKM running-sigma certificate.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-- The full-beta-vector source-law CKM phase equation for a candidate
running sigma. -/
def SourceLawCKMRunningSigmaSolution (σ : ℚ) : Prop :=
  (2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis) * σ =
    cpRawPhaseClaim ℚ

/-- The source-law CKM depth coefficient is the same `386` emitted by the CKM
matrix phase-depth producer. -/
theorem sourceLawCKMDepthCoefficient_eq_matrixDepth :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
      (ckmJarlskogDepthFromMatrix : ℚ) := by
  calc
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
        (386 : ℚ) := fullBetaVectorPoincareOneAxis_ckmDepthSum
    _ = (ckmJarlskogDepthFromMatrix : ℚ) := by
      rw [ckmJarlskogDepthFromMatrix_rat_eq_386]

/-- THEOREM 1: the source-law CKM phase equation uniquely selects the exact
running sigma. -/
theorem sourceLawCKMRunningSigmaSolution_iff_exact (σ : ℚ) :
    SourceLawCKMRunningSigmaSolution σ ↔
      σ = sigmaGUTTwoLoopExact ℚ := by
  unfold SourceLawCKMRunningSigmaSolution
  rw [sourceLawCKMDepthCoefficient_eq_matrixDepth]
  exact ckmMatrixRunningSigmaSolution_iff_exact σ

/-- THEOREM 2: the exact running sigma solves the source-law CKM phase
equation. -/
theorem sigmaGUTTwoLoopExact_solves_sourceLawCKMPhase :
    SourceLawCKMRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ) :=
  (sourceLawCKMRunningSigmaSolution_iff_exact
    (sigmaGUTTwoLoopExact ℚ)).mpr rfl

/-- THEOREM 3: nominal `13/1000` is not the exact source-law phase solution. -/
theorem sigmaGUTNominal_not_sourceLawCKMPhase_solution :
    ¬ SourceLawCKMRunningSigmaSolution (sigmaGUTNominal ℚ) := by
  intro h
  have hsigma :=
    (sourceLawCKMRunningSigmaSolution_iff_exact
      (sigmaGUTNominal ℚ)).mp h
  norm_num [sigmaGUTNominal, sigmaGUTTwoLoopExact] at hsigma

/-- THEOREM 4: rounded decimal proxy `0.01328 = 83/6250` is not the exact
source-law phase solution. -/
theorem sigmaGUTTwoLoopDecimalProxy_not_sourceLawCKMPhase_solution :
    ¬ SourceLawCKMRunningSigmaSolution (sigmaGUTTwoLoopDecimalProxy ℚ) := by
  intro h
  have hsigma :=
    (sourceLawCKMRunningSigmaSolution_iff_exact
      (sigmaGUTTwoLoopDecimalProxy ℚ)).mp h
  norm_num [sigmaGUTTwoLoopDecimalProxy, sigmaGUTTwoLoopExact] at hsigma

/-- THEOREM 5: source-law CKM depth times exact running sigma gives the raw
phase. -/
theorem sourceLawCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim :
    (2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  exact sigmaGUTTwoLoopExact_solves_sourceLawCKMPhase

/-- The upstream source-law CKM sigma producer certificate. -/
structure SourceLawCKMRunningSigmaProducerCertificate : Prop where
  source_law :
    OneAxisFiniteSourceLaw fullBetaVectorPoincareOneAxis
  source_axis_value :
    fullBetaVectorPoincareOneAxis = (10 : ℚ)
  source_depth_coefficient :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
      (386 : ℚ)
  source_depth_matches_matrix :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
      (ckmJarlskogDepthFromMatrix : ℚ)
  source_depth_times_exact_sigma_raw_phase :
    (2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ
  solution_iff_exact :
    ∀ σ : ℚ,
      SourceLawCKMRunningSigmaSolution σ ↔
        σ = sigmaGUTTwoLoopExact ℚ
  exact_solves :
    SourceLawCKMRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ)
  nominal_rejected :
    ¬ SourceLawCKMRunningSigmaSolution (sigmaGUTNominal ℚ)
  decimal_proxy_rejected :
    ¬ SourceLawCKMRunningSigmaSolution (sigmaGUTTwoLoopDecimalProxy ℚ)
  matrix_level_lock :
    CKMRunningSigmaProducerCertificate

/-- THEOREM 6: canonical source-law CKM running-sigma producer. -/
theorem sourceLawCKMRunningSigmaProducerCertificate :
    SourceLawCKMRunningSigmaProducerCertificate where
  source_law :=
    fullBetaVectorPoincareOneAxis_sourceLaw
  source_axis_value :=
    fullBetaVectorPoincareOneAxis_eq_ten
  source_depth_coefficient :=
    fullBetaVectorPoincareOneAxis_ckmDepthSum
  source_depth_matches_matrix :=
    sourceLawCKMDepthCoefficient_eq_matrixDepth
  source_depth_times_exact_sigma_raw_phase :=
    sourceLawCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
  solution_iff_exact :=
    sourceLawCKMRunningSigmaSolution_iff_exact
  exact_solves :=
    sigmaGUTTwoLoopExact_solves_sourceLawCKMPhase
  nominal_rejected :=
    sigmaGUTNominal_not_sourceLawCKMPhase_solution
  decimal_proxy_rejected :=
    sigmaGUTTwoLoopDecimalProxy_not_sourceLawCKMPhase_solution
  matrix_level_lock :=
    ckmRunningSigmaProducerCertificate

end StandardModelConstraint
end SaturationMonoid
