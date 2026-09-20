import H0mework.Physics.JointSources.P787

/-!
# Proposition 788: CKM matrix object identity producer

P761 builds the CKM phase-depth matrix object.  P784 proves the closed
four-card structural source for the Jarlskog phase-depth.  P787 welds that
source to the accepted three-nail input surface.

This file turns those adjacent facts into one matrix-object identity producer:
the matrix object, the four-card structural source, the source-law coefficient,
and every accepted input-surface CKM readout carry the same depth and raw
phase.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Matrix object / four-card / source-law identity -/

/-- THEOREM 1: the matrix-level Jarlskog depth is the closed four-card
structural depth. -/
theorem ckmMatrixDepth_eq_fourCardClosedDepth :
    ckmJarlskogDepthFromMatrix = ckmJarlskogFourCardClosedDepthSum := by
  exact ckmJarlskogFourCardClosedDepthSum_eq_matrixDepth.symm

/-- THEOREM 2: the Mathlib matrix-object Jarlskog readout is the same closed
four-card structural depth. -/
theorem ckmMatrixObjectDepth_eq_fourCardClosedDepth :
    ckmJarlskogDepthFromMatrixObject =
      ckmJarlskogFourCardClosedDepthSum := by
  rw [ckmJarlskogDepthFromMatrixObject_eq_matrix]
  exact ckmMatrixDepth_eq_fourCardClosedDepth

/-- THEOREM 3: the full-beta-vector source-law coefficient is the matrix
object's Jarlskog depth. -/
theorem sourceLawCKMDepthCoefficient_eq_matrixObjectDepth :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
      (ckmJarlskogDepthFromMatrixObject : ℚ) := by
  calc
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
        (ckmJarlskogFourCardClosedDepthSum : ℚ) := by
          exact sourceLawCKMDepthCoefficient_eq_fourCardClosedDepth
    _ = (ckmJarlskogDepthFromMatrixObject : ℚ) := by
          rw [ckmMatrixObjectDepth_eq_fourCardClosedDepth]

/-- THEOREM 4: the four-card structural raw phase is exactly the matrix-object
raw phase. -/
theorem fourCardCKMDepth_mul_sigmaGUTTwoLoopExact_eq_matrixObjectRawPhase :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      (ckmJarlskogDepthFromMatrixObject : ℚ) *
        sigmaGUTTwoLoopExact ℚ := by
  rw [ckmMatrixObjectDepth_eq_fourCardClosedDepth]

/-- THEOREM 5: the matrix-object CKM raw phase is the claimed raw phase. -/
theorem ckmMatrixObjectDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim :
    (ckmJarlskogDepthFromMatrixObject : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  rw [ckmJarlskogDepthFromMatrixObject_eq_matrix]
  exact ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim

/-! ## Accepted input surface reads the same matrix object -/

/-- THEOREM 6: every accepted input-surface CKM depth is the matrix-object
Jarlskog readout. -/
theorem inputSurface_ckmDepth_eq_matrixObjectDepth
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 =
      ckmJarlskogDepthFromMatrixObject :=
  inputSurface_ckmDepth_eq_matrixObjectDepth_int C hC

/-- THEOREM 7: every accepted input-surface CKM raw phase is the matrix-object
raw phase. -/
theorem inputSurface_ckmRawPhase_eq_matrixObjectDepth
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      (ckmJarlskogDepthFromMatrixObject : ℚ) *
        sigmaGUTTwoLoopExact ℚ := by
  rw [inputSurface_ckmDepth_eq_matrixObjectDepth C hC]

/-- THEOREM 8: every accepted input-surface CKM raw phase is the claimed raw
phase through the matrix object. -/
theorem inputSurface_ckmRawPhase_eq_rawPhaseClaim_via_matrixObject
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  rw [inputSurface_ckmRawPhase_eq_matrixObjectDepth C hC]
  exact ckmMatrixObjectDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim

/-! ## Bundled matrix identity certificate -/

/-- One certificate saying the CKM phase-depth producer is a matrix object, not
only a scalar phase sum: the `Matrix` object, four-card source, source-law
coefficient, and accepted input surface are all the same producer readout. -/
structure CKMMatrixObjectIdentityProducerCertificate where
  matrix_producer :
    CKMPhaseDepthMatrixProducerCertificate
  ckm_phase_source_normal_form :
    CKMPhaseProducerSourceNormalFormCertificate
  physicalized_ckm_phase :
    PhysicalizedCKMPhaseProducerCertificate
  ckm_no_free_structural_source :
    CKMJarlskogNoFreeStructuralSourceCertificate
  three_nail_identity_spine :
    GrandUnification.ConcreteThreeNailProducerIdentitySpineCertificate
  matrix_object_closed :
    ckmPhaseDepthMatrixObject = ckmPhaseDepthClosedMatrixObject
  matrix_rows :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]]
  matrix_depth_eq_four_card :
    ckmJarlskogDepthFromMatrix = ckmJarlskogFourCardClosedDepthSum
  matrix_object_depth_eq_four_card :
    ckmJarlskogDepthFromMatrixObject =
      ckmJarlskogFourCardClosedDepthSum
  source_law_eq_matrix_object :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
      (ckmJarlskogDepthFromMatrixObject : ℚ)
  four_card_raw_phase_eq_matrix_object :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      (ckmJarlskogDepthFromMatrixObject : ℚ) *
        sigmaGUTTwoLoopExact ℚ
  matrix_object_raw_phase :
    (ckmJarlskogDepthFromMatrixObject : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ
  input_surface_matrix_object_depth :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 =
          ckmJarlskogDepthFromMatrixObject
  input_surface_matrix_object_raw_phase :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          (ckmJarlskogDepthFromMatrixObject : ℚ) *
            sigmaGUTTwoLoopExact ℚ
  input_surface_raw_phase_claim :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          cpRawPhaseClaim ℚ

/-- DEFINITION 9: CKM matrix-object identity producer certificate. -/
def ckmMatrixObjectIdentityProducerCertificate :
    CKMMatrixObjectIdentityProducerCertificate where
  matrix_producer :=
    ckmPhaseDepthMatrixProducerCertificate
  ckm_phase_source_normal_form :=
    ckmPhaseProducerSourceNormalFormCertificate
  physicalized_ckm_phase :=
    physicalizedCKMPhaseProducerCertificate
  ckm_no_free_structural_source :=
    ckmJarlskogNoFreeStructuralSourceCertificate
  three_nail_identity_spine :=
    GrandUnification.concreteThreeNailProducerIdentitySpineCertificate
  matrix_object_closed :=
    ckmPhaseDepthMatrixObject_eq_closed
  matrix_rows :=
    ckmPhaseDepthMatrixRows_eq
  matrix_depth_eq_four_card :=
    ckmMatrixDepth_eq_fourCardClosedDepth
  matrix_object_depth_eq_four_card :=
    ckmMatrixObjectDepth_eq_fourCardClosedDepth
  source_law_eq_matrix_object :=
    sourceLawCKMDepthCoefficient_eq_matrixObjectDepth
  four_card_raw_phase_eq_matrix_object :=
    fourCardCKMDepth_mul_sigmaGUTTwoLoopExact_eq_matrixObjectRawPhase
  matrix_object_raw_phase :=
    ckmMatrixObjectDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
  input_surface_matrix_object_depth :=
    inputSurface_ckmDepth_eq_matrixObjectDepth
  input_surface_matrix_object_raw_phase :=
    inputSurface_ckmRawPhase_eq_matrixObjectDepth
  input_surface_raw_phase_claim :=
    inputSurface_ckmRawPhase_eq_rawPhaseClaim_via_matrixObject

end StandardModelConstraint
end SaturationMonoid
