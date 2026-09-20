import H0mework.Physics.MixingSources.P768

/-!
# Proposition 769: input-surface finite numerical closure

P768 locks the exact CKM running sigma for every accepted full-beta-vector
input surface.

This file packages the whole finite numerical chain at that same input
surface:

* the input trace axis is `10`;
* the alpha gap is `89/10000`;
* the alpha inverse residual is `-89000/128511`;
* the displayed strong coupling is closed;
* the nine Yukawa depths are forced;
* the CKM/Jarlskog depth is `386`;
* the CKM phase equation has the unique exact running sigma
  `2563/193000`.

So after the input-level product-surface gate, the current finite producer
chain has no remaining presentation freedom.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-- THEOREM 1: accepted input surfaces force the trace/Poincare axis `10`. -/
theorem inputSurfaceFiniteNumerical_axis_eq_ten
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ) :=
  fullBetaVectorInputThreeNailProducerSurface_inputAxis_eq_ten C hC

/-- THEOREM 2: accepted input surfaces force the alpha gap `89/10000`. -/
theorem inputSurfaceFiniteNumerical_alphaGap_eq
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.1.producedGap = (89 : ℚ) / 10000 :=
  fullBetaVectorInputThreeNailProducerSurface_alphaGap C hC

/-- THEOREM 3: accepted input surfaces force the alpha inverse residual. -/
theorem inputSurfaceFiniteNumerical_alphaInverseResidual_eq
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.1.producedGap =
      -((89000 : ℚ) / 128511) :=
  fullBetaVectorInputThreeNailProducerSurface_alphaInverseResidual C hC

/-- THEOREM 4: accepted input surfaces close the displayed strong coupling. -/
theorem inputSurfaceFiniteNumerical_closesDisplayedAlpha
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap) =
      alphaStrongDisplayed ℚ :=
  fullBetaVectorInputThreeNailProducerSurface_closesDisplayedAlpha C hC

/-- THEOREM 5: accepted input surfaces force the nine Yukawa depths. -/
theorem inputSurfaceFiniteNumerical_yukawaMassOrder_eq
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  fullBetaVectorInputThreeNailSurfaceCertificate.yukawa_mass_order C hC

/-- THEOREM 6: accepted input surfaces force the CKM/Jarlskog depth sum as an
integer. -/
theorem inputSurfaceFiniteNumerical_ckmDepthSum_eq_386_int
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int) :=
  fullBetaVectorInputThreeNailSurfaceCertificate.ckm_jarlskog_sum C hC

/-- THEOREM 7: accepted input surfaces force the CKM/Jarlskog depth sum as the
rational number `386`. -/
theorem inputSurfaceFiniteNumerical_ckmDepthSum_eq_386_rat
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) = (386 : ℚ) := by
  have hckm :
      ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int) :=
    inputSurfaceFiniteNumerical_ckmDepthSum_eq_386_int C hC
  rw [hckm]
  norm_num [ckmCPDepthSum]

/-- THEOREM 8: accepted input surfaces project to the canonical finite output. -/
theorem inputSurfaceFiniteNumerical_output_eq_canonical
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    finiteOutputOfFullBetaVectorInput C =
      canonicalSourceLawFinitePhysicalOutput :=
  finiteOutputOfFullBetaVectorInput_eq_canonical C hC

/-- THEOREM 9: accepted input surfaces lock the exact running sigma in the CKM
phase equation. -/
theorem inputSurfaceFiniteNumerical_sigma_solution_iff_exact
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C)
    (σ : ℚ) :
    InputSurfaceCKMRunningSigmaSolution C σ ↔
      σ = sigmaGUTTwoLoopExact ℚ :=
  inputSurfaceCKMRunningSigmaSolution_iff_exact C hC σ

/-- THEOREM 10: accepted input-surface CKM depth times the exact sigma gives
the raw phase. -/
theorem inputSurfaceFiniteNumerical_rawPhase_eq
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ :=
  inputSurfaceCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim C hC

/-- The complete finite numerical closure at the accepted input surface. -/
structure InputSurfaceFiniteNumericalClosureCertificate where
  input_surface :
    FullBetaVectorInputThreeNailSurfaceCertificate
  input_output_bridge :
    InputOutputFiniteBridgeNoFreeCertificate
  ckm_running_sigma :
    InputSurfaceCKMRunningSigmaProducerCertificate
  surface_iff_canonical :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ↔
        C = canonicalFullBetaVectorInputThreeNailCandidate
  no_free :
    NoContinuousFreeFullBetaVectorInputThreeNailParameters
      FullBetaVectorInputThreeNailProducerSurface
  output_eq_canonical :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        finiteOutputOfFullBetaVectorInput C =
          canonicalSourceLawFinitePhysicalOutput
  axis_eq_ten :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ)
  alpha_gap_eq :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.1.producedGap = (89 : ℚ) / 10000
  alpha_inverse_residual :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap =
          -((89000 : ℚ) / 128511)
  alpha_closes_displayed :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                C.1.producedGap) =
          alphaStrongDisplayed ℚ
  yukawa_mass_order :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2.massOrder =
          [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum_int :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int)
  ckm_depth_sum_rat :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) = (386 : ℚ)
  ckm_sigma_solution_iff_exact :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ∀ σ : ℚ,
          InputSurfaceCKMRunningSigmaSolution C σ ↔
            σ = sigmaGUTTwoLoopExact ℚ
  ckm_raw_phase :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          cpRawPhaseClaim ℚ

/-- DEFINITION 1: the accepted input surface closes the whole finite numerical
producer chain. -/
def inputSurfaceFiniteNumericalClosureCertificate :
    InputSurfaceFiniteNumericalClosureCertificate where
  input_surface :=
    fullBetaVectorInputThreeNailSurfaceCertificate
  input_output_bridge :=
    inputOutputFiniteBridgeNoFreeCertificate
  ckm_running_sigma :=
    inputSurfaceCKMRunningSigmaProducerCertificate
  surface_iff_canonical :=
    fullBetaVectorInputThreeNailSurfaceCertificate.surface_iff_canonical
  no_free :=
    fullBetaVectorInputThreeNailSurfaceCertificate.no_free
  output_eq_canonical :=
    inputSurfaceFiniteNumerical_output_eq_canonical
  axis_eq_ten :=
    inputSurfaceFiniteNumerical_axis_eq_ten
  alpha_gap_eq :=
    inputSurfaceFiniteNumerical_alphaGap_eq
  alpha_inverse_residual :=
    inputSurfaceFiniteNumerical_alphaInverseResidual_eq
  alpha_closes_displayed :=
    inputSurfaceFiniteNumerical_closesDisplayedAlpha
  yukawa_mass_order :=
    inputSurfaceFiniteNumerical_yukawaMassOrder_eq
  ckm_depth_sum_int :=
    inputSurfaceFiniteNumerical_ckmDepthSum_eq_386_int
  ckm_depth_sum_rat :=
    inputSurfaceFiniteNumerical_ckmDepthSum_eq_386_rat
  ckm_sigma_solution_iff_exact :=
    inputSurfaceFiniteNumerical_sigma_solution_iff_exact
  ckm_raw_phase :=
    inputSurfaceFiniteNumerical_rawPhase_eq

end StandardModelConstraint
end SaturationMonoid
