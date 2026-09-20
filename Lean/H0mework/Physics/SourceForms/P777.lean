import H0mework.Physics.MixingSources.P776

/-!
# Proposition 777: Standard-Model three-nail producer source normal form

P775, P774, and P776 close the three concrete producer nails separately:

* the `alpha_s` inverse residual is sourced by the full beta-vector color axis
  and the singleton SU(7)-breaking source;
* the nine Yukawa depths are sourced by the unique carrier coefficient stencil;
* the CKM matrix/phase is sourced by that Yukawa table, the source-law axis,
  and the exact running sigma.

This file compresses those three source-normal-form certificates into one
strong three-nail certificate.  Its input-surface theorem is the useful root:
any accepted full-beta-vector three-nail surface carries all three normal forms
simultaneously.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Three-nail input-surface normal form -/

/-- THEOREM 1: every accepted full-beta-vector three-nail input surface
simultaneously carries the alpha, Yukawa, and CKM source normal forms. -/
theorem standardModelThreeNailSourceNormalForm_inputSurface
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ) ∧
        C.1.producedGap = (89 : ℚ) / 10000 ∧
          inverseCorrectionFromAlphaGap
              (alphaStrongTwoLoopSMOutput ℚ)
              C.1.producedGap =
            -((89000 : ℚ) / 128511) ∧
            (1 : ℚ) /
                (alphaStrongTwoLoopSMOutputInverse ℚ +
                  inverseCorrectionFromAlphaGap
                    (alphaStrongTwoLoopSMOutput ℚ)
                    C.1.producedGap) =
              alphaStrongDisplayed ℚ) ∧
      (C.2 = selectedYukawaDepthTableCandidate ∧
        carrierCoefficientYukawaDepthGrid = selectedYukawaDepthGrid ∧
          rationalGridMassOrder carrierCoefficientYukawaDepthGrid =
            [50, 346, 372, 489, 583, 682, 880, 908, 982]) ∧
        ((ckmJarlskogFourProductDepthSum C.2 : ℚ) =
            (ckmJarlskogDepthFromMatrix : ℚ) ∧
          (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
              sigmaGUTTwoLoopExact ℚ =
            cpRawPhaseClaim ℚ ∧
            (∀ σ : ℚ,
              InputSurfaceCKMRunningSigmaSolution C σ ↔
                σ = sigmaGUTTwoLoopExact ℚ) ∧
              ¬ InputSurfaceCKMRunningSigmaSolution C
                  (sigmaGUTNominal ℚ) ∧
                ¬ InputSurfaceCKMRunningSigmaSolution C
                  (sigmaGUTTwoLoopDecimalProxy ℚ)) ∧
          ((CKMJarlskogFactor.depthContribution C.2 .V_us = (-226 : Int) ∧
              CKMJarlskogFactor.depthContribution C.2 .V_cb = (-143 : Int) ∧
                CKMJarlskogFactor.depthContribution C.2 .V_ub_conj =
                  (562 : Int) ∧
                  CKMJarlskogFactor.depthContribution C.2 .V_cs_conj =
                    (193 : Int)) ∧
            ckmJarlskogFourProductDepthSum C.2 =
              ckmJarlskogDepthFromMatrix ∧
              (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
                  sigmaGUTTwoLoopExact ℚ =
                (ckmJarlskogDepthFromMatrix : ℚ) *
                  sigmaGUTTwoLoopExact ℚ) := by
  exact
    ⟨alphaStrongResidualProducerNormalForm_inputSurface C hC,
      inputSurface_yukawaTable_eq_carrierNormalForm C hC,
      ckmPhaseProducerNormalForm_inputSurfaceSigmaLock C hC,
      ckmPhaseProducerNormalForm_inputSurfaceMatrixPhase C hC⟩

/-! ## Bundled certificate -/

/-- One certificate for the three source-normal-form producer nails. -/
structure StandardModelThreeNailProducerSourceNormalFormCertificate : Prop where
  alpha :
    AlphaStrongResidualProducerSourceNormalFormCertificate
  yukawa :
    YukawaDepthProducerSourceNormalFormCertificate
  ckm :
    CKMPhaseProducerSourceNormalFormCertificate
  complete_input_surface :
    InputSurfaceCompleteSourceNormalFormCertificate
  alpha_source :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.toFourSourceClosureReceipt =
        alphaStrongCanonicalFourSourceReceipt ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking =
        (89 : ℚ) / 10000 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
              .threshold = 0 ∧
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
              .threeLoopRG = 0 ∧
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
                .higgsExtraRepresentation = 0 ∧
              (∀ s : AlphaStrongResidualSource,
                AlphaStrongActiveResidualSource
                    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
                  s = .su7Breaking)
  alpha_closure :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) ∧
      (1 : ℚ) /
          (alphaStrongTwoLoopSMOutputInverse ℚ +
            inverseCorrectionFromAlphaGap
              (alphaStrongTwoLoopSMOutput ℚ)
              alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
        alphaStrongDisplayed ℚ
  yukawa_unique_stencil :
    ∃! C : RationalYukawaBiquadraticStencil,
      ∀ g s,
        C.eval g s =
          (selectedYukawaIntegerDepthZ (yukawaMatrixParameter g s) : ℚ)
  yukawa_mass_order :
    rationalGridMassOrder carrierCoefficientYukawaDepthGrid =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  yukawa_jarlskog_depth :
    ckmJarlskogDepthSumFromRationalGrid
        carrierCoefficientYukawaDepthGrid =
      (386 : ℚ)
  ckm_matrix_rows :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]]
  ckm_phase_values :
    sigmaGUTTwoLoopExact ℚ = (2563 : ℚ) / 193000 ∧
      cpRawPhaseClaim ℚ = (5126 : ℚ) / 1000 ∧
        (ckmJarlskogDepthFromMatrix : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          cpRawPhaseClaim ℚ ∧
          cpDeltaCPClaim ℚ =
            cpTauProxy ℚ -
              (ckmJarlskogDepthFromMatrix : ℚ) *
                sigmaGUTTwoLoopExact ℚ ∧
            cpMeasurementNominal ℚ - cpDeltaCPClaim ℚ =
              (43 : ℚ) / 1000 ∧
              ((cpMeasurementNominal ℚ - cpDeltaCPClaim ℚ) /
                  cpMeasurementNominal ℚ) * (100 : ℚ) =
                (43 : ℚ) / 12
  input_surface :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ) ∧
            C.1.producedGap = (89 : ℚ) / 10000 ∧
              inverseCorrectionFromAlphaGap
                  (alphaStrongTwoLoopSMOutput ℚ)
                  C.1.producedGap =
                -((89000 : ℚ) / 128511) ∧
                (1 : ℚ) /
                    (alphaStrongTwoLoopSMOutputInverse ℚ +
                      inverseCorrectionFromAlphaGap
                        (alphaStrongTwoLoopSMOutput ℚ)
                        C.1.producedGap) =
                  alphaStrongDisplayed ℚ) ∧
          (C.2 = selectedYukawaDepthTableCandidate ∧
            carrierCoefficientYukawaDepthGrid = selectedYukawaDepthGrid ∧
              rationalGridMassOrder carrierCoefficientYukawaDepthGrid =
                [50, 346, 372, 489, 583, 682, 880, 908, 982]) ∧
            ((ckmJarlskogFourProductDepthSum C.2 : ℚ) =
                (ckmJarlskogDepthFromMatrix : ℚ) ∧
              (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
                  sigmaGUTTwoLoopExact ℚ =
                cpRawPhaseClaim ℚ ∧
                (∀ σ : ℚ,
                  InputSurfaceCKMRunningSigmaSolution C σ ↔
                    σ = sigmaGUTTwoLoopExact ℚ) ∧
                  ¬ InputSurfaceCKMRunningSigmaSolution C
                      (sigmaGUTNominal ℚ) ∧
                    ¬ InputSurfaceCKMRunningSigmaSolution C
                      (sigmaGUTTwoLoopDecimalProxy ℚ)) ∧
              ((CKMJarlskogFactor.depthContribution C.2 .V_us =
                    (-226 : Int) ∧
                  CKMJarlskogFactor.depthContribution C.2 .V_cb =
                    (-143 : Int) ∧
                    CKMJarlskogFactor.depthContribution C.2 .V_ub_conj =
                      (562 : Int) ∧
                      CKMJarlskogFactor.depthContribution C.2 .V_cs_conj =
                        (193 : Int)) ∧
                ckmJarlskogFourProductDepthSum C.2 =
                  ckmJarlskogDepthFromMatrix ∧
                  (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
                      sigmaGUTTwoLoopExact ℚ =
                    (ckmJarlskogDepthFromMatrix : ℚ) *
                      sigmaGUTTwoLoopExact ℚ)

/-- THEOREM 2: the strong three-nail source-normal-form producer
certificate. -/
theorem standardModelThreeNailProducerSourceNormalFormCertificate :
    StandardModelThreeNailProducerSourceNormalFormCertificate where
  alpha :=
    alphaStrongResidualProducerSourceNormalFormCertificate
  yukawa :=
    yukawaDepthProducerSourceNormalFormCertificate
  ckm :=
    ckmPhaseProducerSourceNormalFormCertificate
  complete_input_surface :=
    inputSurfaceCompleteSourceNormalFormCertificate
  alpha_source :=
    alphaStrongResidualProducerNormalForm_unifiedAxisSource
  alpha_closure :=
    alphaStrongResidualProducerNormalForm_unifiedAxisClosure
  yukawa_unique_stencil :=
    yukawaDepthProducerNormalForm_unique_stencil
  yukawa_mass_order :=
    yukawaDepthProducerNormalForm_massOrder
  yukawa_jarlskog_depth :=
    yukawaDepthProducerNormalForm_jarlskogDepth
  ckm_matrix_rows :=
    ckmPhaseProducerNormalForm_matrixRows
  ckm_phase_values :=
    ckmPhaseProducerNormalForm_phaseValues
  input_surface :=
    standardModelThreeNailSourceNormalForm_inputSurface

end StandardModelConstraint
end SaturationMonoid
