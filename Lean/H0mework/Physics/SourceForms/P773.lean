import H0mework.Physics.MixingSources.P772

/-!
# Proposition 773: complete input-surface source normal form

P770 welds the accepted input surface to the physicalized finite spine.
P771 decomposes the alpha leg to the singleton SU(7)-breaking source.
P772 decomposes the Yukawa/CKM leg to the selected primitive-card endpoint
schedule and CKM matrix/raw-phase normal form.

This file packages those three welds into one source-normal-form root.  The
accepted input surface now has one public certificate for the whole finite
producer ledger:

* singleton/no-free input surface;
* coordinate-spine finite output;
* alpha source normal form;
* Yukawa primitive-card endpoint schedule normal form;
* CKM factor/matrix/raw-phase normal form.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-- THEOREM 1: every accepted input surface is the canonical input product. -/
theorem inputSurface_completeNormalForm_surface_iff_canonical
    (C : FullBetaVectorInputThreeNailCandidate) :
    FullBetaVectorInputThreeNailProducerSurface C ↔
      C = canonicalFullBetaVectorInputThreeNailCandidate :=
  fullBetaVectorInputThreeNailProducerSurface_iff_canonical C

/-- THEOREM 2: every accepted input surface emits the coordinate-spine finite
output from P707. -/
theorem inputSurface_completeNormalForm_outputAxis
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (finiteOutputOfFullBetaVectorInput C).axis =
      GrandUnification.traceWeightedQCDPoincareCoordinateAxis :=
  inputSurface_finiteOutput_axis_eq_coordinateSpine C hC

/-- THEOREM 3: every accepted input surface carries the singleton SU7 alpha
source and the canonical primitive-card Yukawa/CKM endpoint schedule. -/
theorem inputSurface_completeNormalForm_alphaAndYukawa
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.1.producedGap =
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking ∧
      C.2 =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector
            canonicalYukawaCoefficientPrimitiveCardPacket)
          yukawaSectorInformationIncidence := by
  exact
    ⟨inputSurface_alphaGap_eq_su7BreakingContribution C hC,
      inputSurface_yukawaTable_eq_canonicalCoefficientEndpointSchedule C hC⟩

/-- THEOREM 4: every accepted input surface carries the CKM factor quartet and
matrix/raw-phase normal form. -/
theorem inputSurface_completeNormalForm_ckmMatrixPhase
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (CKMJarlskogFactor.depthContribution C.2 .V_us = (-226 : Int) ∧
        CKMJarlskogFactor.depthContribution C.2 .V_cb = (-143 : Int) ∧
          CKMJarlskogFactor.depthContribution C.2 .V_ub_conj =
            (562 : Int) ∧
            CKMJarlskogFactor.depthContribution C.2 .V_cs_conj =
              (193 : Int)) ∧
      ckmJarlskogFourProductDepthSum C.2 = ckmJarlskogDepthFromMatrix ∧
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          (ckmJarlskogDepthFromMatrix : ℚ) *
            sigmaGUTTwoLoopExact ℚ := by
  exact
    ⟨inputSurface_ckmFactors_forced C hC,
      inputSurface_ckmDepth_eq_matrixDepth_int C hC,
      inputSurface_ckmExactRawPhase_eq_matrix C hC⟩

/-- One certificate for the complete accepted input-surface source normal
form. -/
structure InputSurfaceCompleteSourceNormalFormCertificate : Prop where
  finite_numerical_closure :
    Nonempty InputSurfaceFiniteNumericalClosureCertificate
  physicalized_bridge :
    InputSurfacePhysicalizedProducerBridgeCertificate
  alpha_source_decomposition :
    InputSurfaceAlphaSourceDecompositionCertificate
  yukawa_ckm_source_decomposition :
    InputSurfaceYukawaCKMSourceDecompositionCertificate
  full_beta_vector_input_surface :
    Nonempty FullBetaVectorInputThreeNailSurfaceCertificate
  surface_iff_canonical :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ↔
        C = canonicalFullBetaVectorInputThreeNailCandidate
  no_free :
    NoContinuousFreeFullBetaVectorInputThreeNailParameters
      FullBetaVectorInputThreeNailProducerSurface
  output_axis_eq_coordinate_spine :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (finiteOutputOfFullBetaVectorInput C).axis =
          GrandUnification.traceWeightedQCDPoincareCoordinateAxis
  alpha_and_yukawa_sources :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.1.producedGap =
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
              .su7Breaking ∧
          C.2 =
            coefficientScheduleYukawaDepthTableCandidate
              (primitiveCardYukawaDepthStencilCoefficientVector
                canonicalYukawaCoefficientPrimitiveCardPacket)
              yukawaSectorInformationIncidence
  ckm_matrix_phase_normal_form :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (CKMJarlskogFactor.depthContribution C.2 .V_us = (-226 : Int) ∧
            CKMJarlskogFactor.depthContribution C.2 .V_cb = (-143 : Int) ∧
              CKMJarlskogFactor.depthContribution C.2 .V_ub_conj =
                (562 : Int) ∧
                CKMJarlskogFactor.depthContribution C.2 .V_cs_conj =
                  (193 : Int)) ∧
          ckmJarlskogFourProductDepthSum C.2 = ckmJarlskogDepthFromMatrix ∧
            (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
                sigmaGUTTwoLoopExact ℚ =
              (ckmJarlskogDepthFromMatrix : ℚ) *
                sigmaGUTTwoLoopExact ℚ

/-- THEOREM 5: complete accepted input-surface source normal-form
certificate. -/
theorem inputSurfaceCompleteSourceNormalFormCertificate :
    InputSurfaceCompleteSourceNormalFormCertificate where
  finite_numerical_closure :=
    ⟨inputSurfaceFiniteNumericalClosureCertificate⟩
  physicalized_bridge :=
    inputSurfacePhysicalizedProducerBridgeCertificate
  alpha_source_decomposition :=
    inputSurfaceAlphaSourceDecompositionCertificate
  yukawa_ckm_source_decomposition :=
    inputSurfaceYukawaCKMSourceDecompositionCertificate
  full_beta_vector_input_surface :=
    ⟨fullBetaVectorInputThreeNailSurfaceCertificate⟩
  surface_iff_canonical :=
    inputSurface_completeNormalForm_surface_iff_canonical
  no_free :=
    fullBetaVectorInputThreeNailProducerSurface_noFree
  output_axis_eq_coordinate_spine :=
    inputSurface_completeNormalForm_outputAxis
  alpha_and_yukawa_sources :=
    inputSurface_completeNormalForm_alphaAndYukawa
  ckm_matrix_phase_normal_form :=
    inputSurface_completeNormalForm_ckmMatrixPhase

end StandardModelConstraint
end SaturationMonoid
