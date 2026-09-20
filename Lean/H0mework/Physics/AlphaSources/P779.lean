import H0mework.Physics.AlphaSources.P775
import H0mework.Physics.RepresentationSources.P778

/-!
# Proposition 779: alpha_s residual as SU(7) representation-backed source

P775 already proves the finite `alpha_s` residual normal form: the accepted
four-source surface has a singleton active source `.su7Breaking`, its
contribution is `89/10000`, the threshold/RG/Higgs-extra branches are zero,
and inverse transport gives `-89000/128511`.

P778 separately proves that the SU(7) representation/matter/Higgs carrier
computes the displayed Standard-Model one-loop slopes and carries the same
finite numerical spine.

This file welds those two producer faces into one certificate: the displayed
`alpha_s` inverse residual is not a floating correction term.  It is the
SU(7)-breaking residual source read through the representation-backed
matter/Higgs/RG carrier.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Focused welds -/

/-- THEOREM 1: the `alpha_s` SU(7)-breaking source is the whole nonzero alpha
source, while the threshold, three-loop-RG, and Higgs-extra branches vanish. -/
theorem alphaStrongSU7RepresentationResidual_singleActiveSource :
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
                s = .su7Breaking) := by
  rcases alphaStrongResidualProducerNormalForm_unifiedAxisSource with
    ⟨_hreceipt, hgap, hthreshold, hrg, hhiggs, hactive⟩
  exact ⟨hgap, hthreshold, hrg, hhiggs, hactive⟩

/-- THEOREM 2: the same SU(7)-breaking contribution, transported through the
displayed two-loop SM output coordinate, is exactly the canonical inverse
residual `-89000/128511`. -/
theorem alphaStrongSU7RepresentationResidual_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking) =
      -((89000 : ℚ) / 128511) ∧
      inverseCorrectionFromAlphaGap
          (alphaStrongTwoLoopSMOutput ℚ)
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
        -((89000 : ℚ) / 128511) ∧
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
          alphaStrongDisplayed ℚ := by
  exact
    ⟨inputSurface_su7Contribution_inverseResidual,
      alphaStrongResidualProducerNormalForm_unifiedAxisClosure.1,
      alphaStrongResidualProducerNormalForm_unifiedAxisClosure.2⟩

/-- THEOREM 3: the representation-backed SU(7) carrier supplies the QCD
`b0 = 7` readout on both the incidence carrier and the QCD block input used by
the alpha source normal form. -/
theorem alphaStrongSU7RepresentationResidual_qcdB0 :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = (7 : ℚ) ∧
      betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
        betaCoeff qcdBlockIncidenceOneLoopInput =
          standardModelIncidenceBetaVector.color := by
  exact
    ⟨su7RepresentationMatterHiggsNormalForm_b0Values.1,
      su7RepresentationMatterHiggsNormalForm_numericalSpine.1,
      alphaStrongResidualProducerNormalForm_qcdIsColorProjection.1⟩

/-! ## Bundled certificate -/

/-- One certificate saying the finite `alpha_s` residual is simultaneously
the SU(7)-breaking singleton source and the representation-backed QCD carrier
readout. -/
structure AlphaStrongSU7RepresentationResidualSourceCertificate : Prop where
  alpha_source_normal_form :
    AlphaStrongResidualProducerSourceNormalFormCertificate
  su7_representation_matter_higgs :
    SU7RepresentationMatterHiggsSourceNormalFormCertificate
  qcd_b0 :
    betaCoeff (incidenceCarrierTraceInput .colorSU3) = (7 : ℚ) ∧
      betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
        betaCoeff qcdBlockIncidenceOneLoopInput =
          standardModelIncidenceBetaVector.color
  single_active_source :
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
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking) =
      -((89000 : ℚ) / 128511) ∧
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
  alpha_closure_matches_representation_certificate :
    su7RepresentationMatterHiggsSourceNormalFormCertificate.alpha_closure =
      alphaStrongResidualProducerNormalForm_unifiedAxisClosure

/-- THEOREM 4: alpha strong SU(7)-representation residual source
certificate. -/
theorem alphaStrongSU7RepresentationResidualSourceCertificate :
    AlphaStrongSU7RepresentationResidualSourceCertificate where
  alpha_source_normal_form :=
    alphaStrongResidualProducerSourceNormalFormCertificate
  su7_representation_matter_higgs :=
    su7RepresentationMatterHiggsSourceNormalFormCertificate
  qcd_b0 :=
    alphaStrongSU7RepresentationResidual_qcdB0
  single_active_source :=
    alphaStrongSU7RepresentationResidual_singleActiveSource
  inverse_residual :=
    alphaStrongSU7RepresentationResidual_inverseResidual
  alpha_closure_matches_representation_certificate := by
    rfl

end StandardModelConstraint
end SaturationMonoid
