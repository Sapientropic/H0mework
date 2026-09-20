import H0mework.Physics.AlphaSources.P779
import H0mework.Physics.YukawaSources.P780

/-!
# Proposition 781: grand concrete producer numerical source normal form

P777 packages the three concrete Standard-Model producer nails.  P778 welds
the representation/matter/Higgs carrier to the same numerical spine.  P779
pins the displayed `alpha_s` inverse residual to the singleton SU(7)-breaking
source.  P780 adds the all-target Yukawa leave-one-out harness.

This file is the roof certificate for that chain: alpha, Yukawa, and CKM are
not merely three adjacent facts at the grand root.  They are the three visible
readouts of one concrete source-normal-form spine.
-/

noncomputable section

namespace SaturationMonoid

namespace GrandUnification

open StandardModelConstraint
open RunningSigmaBeta

/-! ## Focused grand concrete source-normal-form projections -/

/-- THEOREM 1: the alpha/Yukawa/CKM closed numerical spine. -/
theorem grandConcreteProducerNumericalSourceNormalForm_values :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
        ckmPhaseDepthMatrixRows =
          [[-28, -226, -562], [391, 193, -143], [830, 632, 296]] ∧
          ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) ∧
            (ckmJarlskogDepthFromMatrix : ℚ) *
                sigmaGUTTwoLoopExact ℚ =
              cpRawPhaseClaim ℚ := by
  exact
    ⟨alphaStrongResidualProducerNormalForm_unifiedAxisClosure.1,
      su7RepresentationMatterHiggsNormalForm_numericalSpine.2.1,
      ckmPhaseProducerNormalForm_matrixRows,
      ckmJarlskogDepthFromMatrix_eq_386,
      ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim⟩

/-- THEOREM 2: the SU(7) representation carrier, alpha residual source, and
Yukawa leave-one-out harness read the same numerical spine. -/
theorem grandConcreteProducerNumericalSourceNormalForm_sources :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = (7 : ℚ) ∧
      betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .su7Breaking =
          (89 : ℚ) / 10000 ∧
          (∀ s : AlphaStrongResidualSource,
            AlphaStrongActiveResidualSource
                alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
              s = .su7Breaking) ∧
            primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
              [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
              ckmJarlskogFourProductDepthSum
                  selectedYukawaDepthTableCandidate =
                (ckmCPDepthSum : Int) := by
  exact
    ⟨su7RepresentationMatterHiggsNormalForm_b0Values.1,
      su7RepresentationMatterHiggsNormalForm_numericalSpine.1,
      alphaStrongSU7RepresentationResidual_singleActiveSource.1,
      alphaStrongSU7RepresentationResidual_singleActiveSource.2.2.2.2,
      yukawaLeaveOneOutNormalForm_depthsAndCKM (E := ℂ) |>.1,
      (yukawaLeaveOneOutNormalForm_depthsAndCKM (E := ℂ)).2.2⟩

/-- THEOREM 3: every accepted full-beta-vector three-nail input surface
inherits the same alpha/Yukawa/CKM source-normal-form readout. -/
theorem grandConcreteProducerNumericalSourceNormalForm_inputSurface
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
                  sigmaGUTTwoLoopExact ℚ) :=
  standardModelThreeNailSourceNormalForm_inputSurface C hC

/-! ## Bundled roof certificate -/

/-- One roof certificate for the concrete producer numerical chain. -/
structure GrandConcreteProducerNumericalSourceNormalFormCertificate : Prop where
  three_nail_source_normal_form :
    StandardModelThreeNailProducerSourceNormalFormCertificate
  su7_representation_matter_higgs :
    SU7RepresentationMatterHiggsSourceNormalFormCertificate
  alpha_su7_residual_source :
    AlphaStrongSU7RepresentationResidualSourceCertificate
  yukawa_leave_one_out :
    Nonempty (YukawaLeaveOneOutSourceNormalFormCertificate ℂ)
  ckm_phase_source_normal_form :
    CKMPhaseProducerSourceNormalFormCertificate
  closed_values :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
        ckmPhaseDepthMatrixRows =
          [[-28, -226, -562], [391, 193, -143], [830, 632, 296]] ∧
          ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) ∧
            (ckmJarlskogDepthFromMatrix : ℚ) *
                sigmaGUTTwoLoopExact ℚ =
              cpRawPhaseClaim ℚ
  source_spine :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = (7 : ℚ) ∧
      betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .su7Breaking =
          (89 : ℚ) / 10000 ∧
          (∀ s : AlphaStrongResidualSource,
            AlphaStrongActiveResidualSource
                alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
              s = .su7Breaking) ∧
            primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
              [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
              ckmJarlskogFourProductDepthSum
                  selectedYukawaDepthTableCandidate =
                (ckmCPDepthSum : Int)
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

/-- THEOREM 4: grand concrete producer numerical source-normal-form
certificate. -/
theorem grandConcreteProducerNumericalSourceNormalFormCertificate :
    GrandConcreteProducerNumericalSourceNormalFormCertificate where
  three_nail_source_normal_form :=
    standardModelThreeNailProducerSourceNormalFormCertificate
  su7_representation_matter_higgs :=
    su7RepresentationMatterHiggsSourceNormalFormCertificate
  alpha_su7_residual_source :=
    alphaStrongSU7RepresentationResidualSourceCertificate
  yukawa_leave_one_out :=
    ⟨yukawaLeaveOneOutSourceNormalFormCertificate (E := ℂ)⟩
  ckm_phase_source_normal_form :=
    ckmPhaseProducerSourceNormalFormCertificate
  closed_values :=
    grandConcreteProducerNumericalSourceNormalForm_values
  source_spine :=
    grandConcreteProducerNumericalSourceNormalForm_sources
  input_surface :=
    grandConcreteProducerNumericalSourceNormalForm_inputSurface

end GrandUnification
end SaturationMonoid
