import H0mework.Physics.AlphaSources.P775

/-!
# Proposition 776: CKM phase producer source normal form

P761 builds the CKM phase-depth matrix from the selected Yukawa depth table.
P765-P768 weld that matrix to the exact running sigma and to the accepted
input surface.  This file packages the whole CKM leg into one normal-form
certificate:

* Yukawa-depth deltas generate the closed `3 x 3` CKM phase-depth matrix;
* the matrix Jarlskog readout is `386`;
* `386 * sigmaGUTTwoLoopExact = 5.126`;
* the unique rational phase solution is `sigmaGUTTwoLoopExact = 2563/193000`;
* nominal `13/1000` and decimal proxy `0.01328` are rejected;
* the complement branch gives the declared `delta_CP` value;
* the same lock is visible at matrix, source-law, and accepted input-surface
  levels.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Focused CKM normal-form projections -/

/-- THEOREM 1: the named Yukawa depth deltas force the Jarlskog depth `386`.
-/
theorem ckmPhaseProducerNormalForm_depthDeltas :
    ckmDepthDelta_us_fromYukawaDepths = ckmCPDepthDelta_us ∧
      ckmDepthDelta_cb_fromYukawaDepths = ckmCPDepthDelta_cb ∧
        ckmDepthDelta_ub_conj_fromYukawaDepths =
          ckmCPDepthDelta_ub_conj ∧
          ckmDepthDelta_cs_conj_fromYukawaDepths =
            ckmCPDepthDelta_cs_conj ∧
            ckmDepthSum_fromYukawaDepths = (ckmCPDepthSum : Int) := by
  exact
    ⟨ckmDepthDelta_us_fromYukawaDepths_eq,
      ckmDepthDelta_cb_fromYukawaDepths_eq,
      ckmDepthDelta_ub_conj_fromYukawaDepths_eq,
      ckmDepthDelta_cs_conj_fromYukawaDepths_eq,
      ckmDepthSum_fromYukawaDepths_eq_386⟩

/-- THEOREM 2: the CKM phase-depth matrix has the closed rows used by the
physicalized producer. -/
theorem ckmPhaseProducerNormalForm_matrixRows :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]] :=
  ckmPhaseDepthMatrixRows_eq

/-- THEOREM 3: the function and Mathlib-matrix CKM objects are both the
closed matrix object. -/
theorem ckmPhaseProducerNormalForm_matrixClosed :
    ckmPhaseDepthMatrix = ckmPhaseDepthMatrixClosed ∧
      ckmPhaseDepthMatrixObject = ckmPhaseDepthClosedMatrixObject :=
  ⟨ckmPhaseDepthMatrix_eq_closed, ckmPhaseDepthMatrixObject_eq_closed⟩

/-- THEOREM 4: matrix-level and object-level Jarlskog reads are both `386`
and agree with the selected Yukawa table. -/
theorem ckmPhaseProducerNormalForm_jarlskog :
    ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) ∧
      ckmJarlskogDepthFromMatrixObject = (ckmCPDepthSum : Int) ∧
        ckmJarlskogDepthFromMatrix =
          ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate ∧
          ckmJarlskogDepthFromMatrixObject =
            ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate ∧
            (ckmJarlskogDepthFromMatrix : ℚ) = (386 : ℚ) := by
  exact
    ⟨ckmJarlskogDepthFromMatrix_eq_386,
      ckmJarlskogDepthFromMatrixObject_eq_386,
      ckmJarlskogDepthFromMatrix_eq_selectedTable,
      ckmJarlskogDepthFromMatrixObject_eq_selectedTable,
      ckmJarlskogDepthFromMatrix_rat_eq_386⟩

/-- THEOREM 5: the matrix-level phase values are fixed:
exact sigma `2563/193000`, raw phase `5.126`, and complement branch `delta_CP`.
-/
theorem ckmPhaseProducerNormalForm_phaseValues :
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
                (43 : ℚ) / 12 := by
  exact
    ⟨ckmRunningSigmaProducerCertificate.exact_sigma_value,
      ckmRunningSigmaProducerCertificate.raw_phase_value,
      ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim,
      cpDeltaCPClaim_eq_tauProxy_minus_ckmMatrixPhase,
      cpDeltaCPClaim_abs_error_to_measurement ℚ,
      cpDeltaCPClaim_percent_error_to_measurement ℚ⟩

/-- THEOREM 6: the matrix-level CKM phase equation has exactly one rational
solution, and both nominal proxy values are rejected. -/
theorem ckmPhaseProducerNormalForm_matrixSigmaLock :
    (∀ σ : ℚ,
        CKMMatrixRunningSigmaSolution σ ↔
          σ = sigmaGUTTwoLoopExact ℚ) ∧
      CKMMatrixRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ) ∧
        ¬ CKMMatrixRunningSigmaSolution (sigmaGUTNominal ℚ) ∧
          ¬ CKMMatrixRunningSigmaSolution
            (sigmaGUTTwoLoopDecimalProxy ℚ) :=
  ⟨ckmMatrixRunningSigmaSolution_iff_exact,
    sigmaGUTTwoLoopExact_solves_ckmMatrixPhase,
    sigmaGUTNominal_not_ckmMatrixPhase_solution,
    sigmaGUTTwoLoopDecimalProxy_not_ckmMatrixPhase_solution⟩

/-- THEOREM 7: the full-beta-vector source-law CKM phase equation carries the
same unique sigma lock. -/
theorem ckmPhaseProducerNormalForm_sourceLawSigmaLock :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
        (ckmJarlskogDepthFromMatrix : ℚ) ∧
      (2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis) *
          sigmaGUTTwoLoopExact ℚ =
        cpRawPhaseClaim ℚ ∧
        (∀ σ : ℚ,
          SourceLawCKMRunningSigmaSolution σ ↔
            σ = sigmaGUTTwoLoopExact ℚ) ∧
          ¬ SourceLawCKMRunningSigmaSolution (sigmaGUTNominal ℚ) ∧
            ¬ SourceLawCKMRunningSigmaSolution
              (sigmaGUTTwoLoopDecimalProxy ℚ) := by
  exact
    ⟨sourceLawCKMDepthCoefficient_eq_matrixDepth,
      sourceLawCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim,
      sourceLawCKMRunningSigmaSolution_iff_exact,
      sigmaGUTNominal_not_sourceLawCKMPhase_solution,
      sigmaGUTTwoLoopDecimalProxy_not_sourceLawCKMPhase_solution⟩

/-- THEOREM 8: every accepted input surface carries the same CKM phase lock.
-/
theorem ckmPhaseProducerNormalForm_inputSurfaceSigmaLock
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) =
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
              (sigmaGUTTwoLoopDecimalProxy ℚ) :=
  ⟨inputSurfaceCKMDepth_eq_matrixDepth C hC,
    inputSurfaceCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim C hC,
    inputSurfaceCKMRunningSigmaSolution_iff_exact C hC,
    sigmaGUTNominal_not_inputSurfaceCKMPhase_solution C hC,
    sigmaGUTTwoLoopDecimalProxy_not_inputSurfaceCKMPhase_solution C hC⟩

/-- THEOREM 9: every accepted input surface inherits the CKM matrix factor
quartet, exact depth, and exact raw phase. -/
theorem ckmPhaseProducerNormalForm_inputSurfaceMatrixPhase
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

/-! ## Bundled certificate -/

/-- One source-normal-form certificate for the CKM matrix / phase producer
leg. -/
structure CKMPhaseProducerSourceNormalFormCertificate : Prop where
  ckm_depth_from_yukawa :
    Nonempty CKMDepthFromYukawaDepthReceipt
  ckm_matrix_producer :
    Nonempty CKMPhaseDepthMatrixProducerCertificate
  physicalized_ckm_phase :
    PhysicalizedCKMPhaseProducerCertificate
  ckm_running_sigma :
    CKMRunningSigmaProducerCertificate
  source_law_ckm_running_sigma :
    SourceLawCKMRunningSigmaProducerCertificate
  input_surface_ckm_running_sigma :
    InputSurfaceCKMRunningSigmaProducerCertificate
  input_surface_yukawa_ckm :
    InputSurfaceYukawaCKMSourceDecompositionCertificate
  yukawa_depth_source_normal_form :
    YukawaDepthProducerSourceNormalFormCertificate
  depth_deltas :
    ckmDepthDelta_us_fromYukawaDepths = ckmCPDepthDelta_us ∧
      ckmDepthDelta_cb_fromYukawaDepths = ckmCPDepthDelta_cb ∧
        ckmDepthDelta_ub_conj_fromYukawaDepths =
          ckmCPDepthDelta_ub_conj ∧
          ckmDepthDelta_cs_conj_fromYukawaDepths =
            ckmCPDepthDelta_cs_conj ∧
            ckmDepthSum_fromYukawaDepths = (ckmCPDepthSum : Int)
  matrix_rows :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]]
  matrix_closed :
    ckmPhaseDepthMatrix = ckmPhaseDepthMatrixClosed ∧
      ckmPhaseDepthMatrixObject = ckmPhaseDepthClosedMatrixObject
  jarlskog :
    ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int) ∧
      ckmJarlskogDepthFromMatrixObject = (ckmCPDepthSum : Int) ∧
        ckmJarlskogDepthFromMatrix =
          ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate ∧
          ckmJarlskogDepthFromMatrixObject =
            ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate ∧
            (ckmJarlskogDepthFromMatrix : ℚ) = (386 : ℚ)
  phase_values :
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
  matrix_sigma_lock :
    (∀ σ : ℚ,
        CKMMatrixRunningSigmaSolution σ ↔
          σ = sigmaGUTTwoLoopExact ℚ) ∧
      CKMMatrixRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ) ∧
        ¬ CKMMatrixRunningSigmaSolution (sigmaGUTNominal ℚ) ∧
          ¬ CKMMatrixRunningSigmaSolution
            (sigmaGUTTwoLoopDecimalProxy ℚ)
  source_law_sigma_lock :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
        (ckmJarlskogDepthFromMatrix : ℚ) ∧
      (2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis) *
          sigmaGUTTwoLoopExact ℚ =
        cpRawPhaseClaim ℚ ∧
        (∀ σ : ℚ,
          SourceLawCKMRunningSigmaSolution σ ↔
            σ = sigmaGUTTwoLoopExact ℚ) ∧
          ¬ SourceLawCKMRunningSigmaSolution (sigmaGUTNominal ℚ) ∧
            ¬ SourceLawCKMRunningSigmaSolution
              (sigmaGUTTwoLoopDecimalProxy ℚ)
  input_surface_sigma_lock :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) =
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
                  (sigmaGUTTwoLoopDecimalProxy ℚ)
  input_surface_matrix_phase :
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

/-- THEOREM 10: finite CKM matrix / phase producer source normal-form
certificate. -/
theorem ckmPhaseProducerSourceNormalFormCertificate :
    CKMPhaseProducerSourceNormalFormCertificate where
  ckm_depth_from_yukawa := ⟨ckmDepthFromYukawaDepthReceipt⟩
  ckm_matrix_producer := ⟨ckmPhaseDepthMatrixProducerCertificate⟩
  physicalized_ckm_phase :=
    physicalizedCKMPhaseProducerCertificate
  ckm_running_sigma :=
    ckmRunningSigmaProducerCertificate
  source_law_ckm_running_sigma :=
    sourceLawCKMRunningSigmaProducerCertificate
  input_surface_ckm_running_sigma :=
    inputSurfaceCKMRunningSigmaProducerCertificate
  input_surface_yukawa_ckm :=
    inputSurfaceYukawaCKMSourceDecompositionCertificate
  yukawa_depth_source_normal_form :=
    yukawaDepthProducerSourceNormalFormCertificate
  depth_deltas :=
    ckmPhaseProducerNormalForm_depthDeltas
  matrix_rows :=
    ckmPhaseProducerNormalForm_matrixRows
  matrix_closed :=
    ckmPhaseProducerNormalForm_matrixClosed
  jarlskog :=
    ckmPhaseProducerNormalForm_jarlskog
  phase_values :=
    ckmPhaseProducerNormalForm_phaseValues
  matrix_sigma_lock :=
    ckmPhaseProducerNormalForm_matrixSigmaLock
  source_law_sigma_lock :=
    ckmPhaseProducerNormalForm_sourceLawSigmaLock
  input_surface_sigma_lock :=
    ckmPhaseProducerNormalForm_inputSurfaceSigmaLock
  input_surface_matrix_phase :=
    ckmPhaseProducerNormalForm_inputSurfaceMatrixPhase

end StandardModelConstraint
end SaturationMonoid
