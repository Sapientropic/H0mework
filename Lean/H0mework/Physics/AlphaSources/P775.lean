import H0mework.Physics.RunningSources.P708
import H0mework.Physics.YukawaSources.P774

/-!
# Proposition 775: alpha_s residual producer source normal form

P660/P771/P773 already prove the alpha leg in pieces:

* the full Standard-Model beta-vector input surface is a singleton;
* the color projection plus the 4D Poincare slots gives the shared axis `10`;
* that axis gives the finite alpha gap `89/10000`;
* the accepted four-source surface has singleton active source `.su7Breaking`;
* the induced inverse-coordinate residual is `-89000/128511`;
* substituting that residual closes the displayed `alpha_s` value.

This file packages those facts into one source-normal-form certificate for the
`alpha_s` producer.  It is the alpha-side twin of P774: the accepted input
surface is no longer merely numerically closed; it is identified with the
input-level full beta-vector carrier and the singleton SU(7)-breaking source.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Focused normal-form projections -/

/-- THEOREM 1: the full incidence beta vector is exactly
`(7, 19/6, -41/6)` in the residual/asymptotic convention. -/
theorem alphaStrongResidualProducerNormalForm_fullBetaVector :
    standardModelIncidenceBetaVector.color = (7 : ℚ) ∧
      standardModelIncidenceBetaVector.weak = (19 : ℚ) / 6 ∧
        standardModelIncidenceBetaVector.hypercharge =
          -((41 : ℚ) / 6) := by
  exact
    ⟨standardModelIncidenceBetaVector_color,
      standardModelIncidenceBetaVector_weak,
      standardModelIncidenceBetaVector_hypercharge⟩

/-- THEOREM 2: the QCD alpha leg is the color projection of the full
beta-vector carrier, both before and after trace-weighting. -/
theorem alphaStrongResidualProducerNormalForm_qcdIsColorProjection :
    betaCoeff qcdBlockIncidenceOneLoopInput =
        standardModelIncidenceBetaVector.color ∧
      applyTraceOneLoopWeights
          standardTraceOneLoopUniversalWeights
          qcdBlockIncidenceOneLoopInput =
        standardModelIncidenceBetaVector.color := by
  exact
    ⟨qcdBlockInput_betaCoeff_eq_fullBetaVector_color,
      qcdBlockInput_traceWeighted_eq_fullBetaVector_color⟩

/-- THEOREM 3: the full beta-vector color projection plus the 4D Poincare
slot count is the shared alpha axis `10`. -/
theorem alphaStrongResidualProducerNormalForm_axis_eq_ten :
    standardModelIncidenceBetaVector.color +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
          ℚ) =
      (10 : ℚ) :=
  fullBetaVectorColorPoincareAxis_eq_ten

/-- THEOREM 4: any accepted input-level full beta-vector alpha candidate is
canonical, has gap `89/10000`, transports to `-89000/128511`, and closes the
displayed strong coupling. -/
theorem alphaStrongResidualProducerNormalForm_inputLevelCandidate
    (C : FullBetaVectorAlphaResidualInputCandidate)
    (hC : FullBetaVectorAlphaResidualInputProducerSurface C) :
    C = canonicalFullBetaVectorAlphaResidualInputCandidate ∧
      C.producedGap = (89 : ℚ) / 10000 ∧
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.producedGap =
          -((89000 : ℚ) / 128511) ∧
          (1 : ℚ) /
              (alphaStrongTwoLoopSMOutputInverse ℚ +
                inverseCorrectionFromAlphaGap
                  (alphaStrongTwoLoopSMOutput ℚ)
                  C.producedGap) =
            alphaStrongDisplayed ℚ := by
  exact
    ⟨eq_canonicalFullBetaVectorAlphaResidualInputCandidate_of_surface C hC,
      fullBetaVectorAlphaResidualInputProducerSurface_gap C hC,
      fullBetaVectorAlphaResidualInputProducerSurface_inverseResidual C hC,
      fullBetaVectorAlphaResidualInputProducerSurface_closes_displayedAlpha C hC⟩

/-- THEOREM 5: every accepted three-nail input surface carries the same alpha
normal form: axis `10`, gap `89/10000`, inverse residual `-89000/128511`, and
displayed-alpha closure. -/
theorem alphaStrongResidualProducerNormalForm_inputSurface
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ) ∧
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
            alphaStrongDisplayed ℚ := by
  exact
    ⟨inputSurfaceFiniteNumerical_axis_eq_ten C hC,
      inputSurfaceFiniteNumerical_alphaGap_eq C hC,
      inputSurfaceFiniteNumerical_alphaInverseResidual_eq C hC,
      inputSurfaceFiniteNumerical_closesDisplayedAlpha C hC⟩

/-- THEOREM 6: the accepted input-surface alpha gap is exactly the singleton
SU(7)-breaking source contribution, and that source carries the whole gap. -/
theorem alphaStrongResidualProducerNormalForm_inputSurfaceSource
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.1.producedGap =
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking ∧
      C.1.producedGap =
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap :=
  ⟨inputSurface_alphaGap_eq_su7BreakingContribution C hC,
    inputSurface_alphaGap_eq_unifiedAxisProducedGap C hC⟩

/-- THEOREM 7: the unified-axis alpha producer has canonical four-source
normal form with singleton active source `.su7Breaking`. -/
theorem alphaStrongResidualProducerNormalForm_unifiedAxisSource :
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
                  s = .su7Breaking) := by
  rcases alphaStrongQCDPoincareUnifiedAxis_nonSU7_sources_zero with
    ⟨hthreshold, hrg, hhiggs⟩
  exact
    ⟨alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_toFourSource_eq_canonical,
      alphaStrongQCDPoincareUnifiedAxis_su7Source_gap,
      hthreshold,
      hrg,
      hhiggs,
      inputSurface_alpha_activeSource_iff_su7Breaking⟩

/-- THEOREM 8: the unified-axis produced gap is the exact inverse residual
and closes the displayed strong coupling. -/
theorem alphaStrongResidualProducerNormalForm_unifiedAxisClosure :
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
    ⟨alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection,
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_closes_displayedAlpha⟩

/-! ## Bundled certificate -/

/-- One source-normal-form certificate for the finite `alpha_s` producer leg.
-/
structure AlphaStrongResidualProducerSourceNormalFormCertificate : Prop where
  full_beta_vector_alpha :
    Nonempty FullBetaVectorAlphaResidualProducerCertificate
  full_beta_vector_alpha_surface :
    Nonempty FullBetaVectorAlphaResidualSurfaceCertificate
  full_beta_vector_alpha_input_surface :
    Nonempty FullBetaVectorAlphaResidualInputSurfaceCertificate
  finite_alpha_numerical :
    Nonempty InputSurfaceFiniteNumericalClosureCertificate
  alpha_source_decomposition :
    InputSurfaceAlphaSourceDecompositionCertificate
  input_surface_complete :
    InputSurfaceCompleteSourceNormalFormCertificate
  active_source_normal_form :
    AlphaStrongActiveSourceNormalFormCertificate
  independent_residual :
    Nonempty AlphaStrongIndependentResidualProducerCertificate
  finite_producer_debt_closure :
    Nonempty AlphaStrongFiniteProducerDebtClosureCertificate
  full_beta_vector :
    standardModelIncidenceBetaVector.color = (7 : ℚ) ∧
      standardModelIncidenceBetaVector.weak = (19 : ℚ) / 6 ∧
        standardModelIncidenceBetaVector.hypercharge =
          -((41 : ℚ) / 6)
  qcd_is_color_projection :
    betaCoeff qcdBlockIncidenceOneLoopInput =
        standardModelIncidenceBetaVector.color ∧
      applyTraceOneLoopWeights
          standardTraceOneLoopUniversalWeights
          qcdBlockIncidenceOneLoopInput =
        standardModelIncidenceBetaVector.color
  axis_eq_ten :
    standardModelIncidenceBetaVector.color +
        (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 :
          ℚ) =
      (10 : ℚ)
  input_level_candidate :
    ∀ C : FullBetaVectorAlphaResidualInputCandidate,
      FullBetaVectorAlphaResidualInputProducerSurface C ->
        C = canonicalFullBetaVectorAlphaResidualInputCandidate ∧
          C.producedGap = (89 : ℚ) / 10000 ∧
            inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                C.producedGap =
              -((89000 : ℚ) / 128511) ∧
              (1 : ℚ) /
                  (alphaStrongTwoLoopSMOutputInverse ℚ +
                    inverseCorrectionFromAlphaGap
                      (alphaStrongTwoLoopSMOutput ℚ)
                      C.producedGap) =
                alphaStrongDisplayed ℚ
  input_surface :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        incidenceBetaInputOneAxis C.1.betaInput = (10 : ℚ) ∧
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
                alphaStrongDisplayed ℚ
  input_surface_source :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.1.producedGap =
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
              .su7Breaking ∧
          C.1.producedGap =
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap
  unified_axis_source :
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
  unified_axis_closure :
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

/-- THEOREM 9: finite `alpha_s` residual producer source normal-form
certificate. -/
theorem alphaStrongResidualProducerSourceNormalFormCertificate :
    AlphaStrongResidualProducerSourceNormalFormCertificate where
  full_beta_vector_alpha := ⟨fullBetaVectorAlphaResidualProducerCertificate⟩
  full_beta_vector_alpha_surface :=
    ⟨fullBetaVectorAlphaResidualSurfaceCertificate⟩
  full_beta_vector_alpha_input_surface :=
    ⟨fullBetaVectorAlphaResidualInputSurfaceCertificate⟩
  finite_alpha_numerical :=
    ⟨inputSurfaceFiniteNumericalClosureCertificate⟩
  alpha_source_decomposition :=
    inputSurfaceAlphaSourceDecompositionCertificate
  input_surface_complete :=
    inputSurfaceCompleteSourceNormalFormCertificate
  active_source_normal_form :=
    alphaStrongActiveSourceNormalFormCertificate
  independent_residual :=
    ⟨alphaStrongIndependentResidualProducerCertificate⟩
  finite_producer_debt_closure :=
    ⟨alphaStrongFiniteProducerDebtClosureCertificate⟩
  full_beta_vector :=
    alphaStrongResidualProducerNormalForm_fullBetaVector
  qcd_is_color_projection :=
    alphaStrongResidualProducerNormalForm_qcdIsColorProjection
  axis_eq_ten :=
    alphaStrongResidualProducerNormalForm_axis_eq_ten
  input_level_candidate :=
    alphaStrongResidualProducerNormalForm_inputLevelCandidate
  input_surface :=
    alphaStrongResidualProducerNormalForm_inputSurface
  input_surface_source :=
    alphaStrongResidualProducerNormalForm_inputSurfaceSource
  unified_axis_source :=
    alphaStrongResidualProducerNormalForm_unifiedAxisSource
  unified_axis_closure :=
    alphaStrongResidualProducerNormalForm_unifiedAxisClosure

end StandardModelConstraint
end SaturationMonoid
