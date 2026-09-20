import H0mework.Physics.SourceForms.P680
import H0mework.Physics.MixingSources.P767

/-!
# Proposition 768: input-surface CKM sigma producer

P767 proves that the source-law CKM phase equation uniquely selects the exact
running sigma.

This file pushes the lock all the way back to the accepted full-beta-vector
input surface.  For any accepted input candidate `C`, the surface certificate
already forces its Jarlskog four-product depth sum to be the same `386` emitted
by the CKM phase matrix.  Therefore the input surface itself carries the same
phase equation:

`ckmJarlskogFourProductDepthSum C.depthTable * sigma = 5.126`.

The unique rational solution is again `sigmaGUTTwoLoopExact = 2563/193000`.
This removes the final input-surface freedom from the CKM running-sigma nail.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-- The input-surface CKM phase equation for a candidate running sigma. -/
def InputSurfaceCKMRunningSigmaSolution
    (C : FullBetaVectorInputThreeNailCandidate) (σ : ℚ) : Prop :=
  (ckmJarlskogFourProductDepthSum C.2 : ℚ) * σ =
    cpRawPhaseClaim ℚ

/-- Accepted input surfaces emit the same CKM/Jarlskog depth as the matrix
phase-depth producer. -/
theorem inputSurfaceCKMDepth_eq_matrixDepth
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) =
      (ckmJarlskogDepthFromMatrix : ℚ) := by
  calc
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) = (386 : ℚ) := by
      have hinput :
          ckmJarlskogFourProductDepthSum C.2 =
            (ckmCPDepthSum : Int) :=
        fullBetaVectorInputThreeNailSurfaceCertificate.ckm_jarlskog_sum C hC
      rw [hinput]
      norm_num [ckmCPDepthSum]
    _ = (ckmJarlskogDepthFromMatrix : ℚ) := by
      rw [ckmJarlskogDepthFromMatrix_rat_eq_386]

/-- THEOREM 1: every accepted input-surface CKM phase equation uniquely selects
the exact running sigma. -/
theorem inputSurfaceCKMRunningSigmaSolution_iff_exact
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C)
    (σ : ℚ) :
    InputSurfaceCKMRunningSigmaSolution C σ ↔
      σ = sigmaGUTTwoLoopExact ℚ := by
  unfold InputSurfaceCKMRunningSigmaSolution
  rw [inputSurfaceCKMDepth_eq_matrixDepth C hC]
  exact ckmMatrixRunningSigmaSolution_iff_exact σ

/-- THEOREM 2: the exact running sigma solves every accepted input-surface CKM
phase equation. -/
theorem sigmaGUTTwoLoopExact_solves_inputSurfaceCKMPhase
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    InputSurfaceCKMRunningSigmaSolution C (sigmaGUTTwoLoopExact ℚ) :=
  (inputSurfaceCKMRunningSigmaSolution_iff_exact C hC
    (sigmaGUTTwoLoopExact ℚ)).mpr rfl

/-- THEOREM 3: nominal `13/1000` is not an accepted input-surface phase
solution. -/
theorem sigmaGUTNominal_not_inputSurfaceCKMPhase_solution
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ¬ InputSurfaceCKMRunningSigmaSolution C (sigmaGUTNominal ℚ) := by
  intro h
  have hsigma :=
    (inputSurfaceCKMRunningSigmaSolution_iff_exact C hC
      (sigmaGUTNominal ℚ)).mp h
  norm_num [sigmaGUTNominal, sigmaGUTTwoLoopExact] at hsigma

/-- THEOREM 4: rounded decimal proxy `0.01328 = 83/6250` is not an accepted
input-surface phase solution. -/
theorem sigmaGUTTwoLoopDecimalProxy_not_inputSurfaceCKMPhase_solution
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ¬ InputSurfaceCKMRunningSigmaSolution C
        (sigmaGUTTwoLoopDecimalProxy ℚ) := by
  intro h
  have hsigma :=
    (inputSurfaceCKMRunningSigmaSolution_iff_exact C hC
      (sigmaGUTTwoLoopDecimalProxy ℚ)).mp h
  norm_num [sigmaGUTTwoLoopDecimalProxy, sigmaGUTTwoLoopExact] at hsigma

/-- THEOREM 5: accepted input-surface depth times exact running sigma gives the
raw phase. -/
theorem inputSurfaceCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  exact sigmaGUTTwoLoopExact_solves_inputSurfaceCKMPhase C hC

/-- The input-level CKM running-sigma producer certificate. -/
structure InputSurfaceCKMRunningSigmaProducerCertificate : Prop where
  source_law_lock :
    SourceLawCKMRunningSigmaProducerCertificate
  input_surface_depth_matches_matrix :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) =
          (ckmJarlskogDepthFromMatrix : ℚ)
  input_surface_depth_times_exact_sigma_raw_phase :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          cpRawPhaseClaim ℚ
  input_surface_solution_iff_exact :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ∀ σ : ℚ,
          InputSurfaceCKMRunningSigmaSolution C σ ↔
            σ = sigmaGUTTwoLoopExact ℚ
  exact_solves :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      ∀ _ : FullBetaVectorInputThreeNailProducerSurface C,
        InputSurfaceCKMRunningSigmaSolution C (sigmaGUTTwoLoopExact ℚ)
  nominal_rejected :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      ∀ _ : FullBetaVectorInputThreeNailProducerSurface C,
        ¬ InputSurfaceCKMRunningSigmaSolution C (sigmaGUTNominal ℚ)
  decimal_proxy_rejected :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      ∀ _ : FullBetaVectorInputThreeNailProducerSurface C,
        ¬ InputSurfaceCKMRunningSigmaSolution C
            (sigmaGUTTwoLoopDecimalProxy ℚ)

/-- THEOREM 6: every accepted full-beta-vector input surface locks the same
exact CKM running sigma. -/
theorem inputSurfaceCKMRunningSigmaProducerCertificate :
    InputSurfaceCKMRunningSigmaProducerCertificate where
  source_law_lock :=
    sourceLawCKMRunningSigmaProducerCertificate
  input_surface_depth_matches_matrix :=
    inputSurfaceCKMDepth_eq_matrixDepth
  input_surface_depth_times_exact_sigma_raw_phase :=
    inputSurfaceCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
  input_surface_solution_iff_exact :=
    inputSurfaceCKMRunningSigmaSolution_iff_exact
  exact_solves :=
    sigmaGUTTwoLoopExact_solves_inputSurfaceCKMPhase
  nominal_rejected :=
    sigmaGUTNominal_not_inputSurfaceCKMPhase_solution
  decimal_proxy_rejected :=
    sigmaGUTTwoLoopDecimalProxy_not_inputSurfaceCKMPhase_solution

end StandardModelConstraint
end SaturationMonoid
