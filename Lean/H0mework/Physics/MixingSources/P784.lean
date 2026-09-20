import H0mework.Physics.MixingSources.P653
import H0mework.Physics.AlphaSources.P783

/-!
# Proposition 784: CKM/Jarlskog no-free structural source normal form

P653 proves the closed four-card CKM/Jarlskog formula

`2 * ((48 - 1) - (-(137 + 9))) = 386`.

P776 proves that the CKM phase-depth matrix, the source-law sector gap, the
accepted input surface, and the exact running sigma all read the same `386`.

This file welds those readings into one no-free structural source certificate:
the four-card sector-axis source surface is a singleton, and its closed formula
is the same object as the matrix-level Jarlskog depth and the source-law phase
equation.  The CKM phase nail is therefore not a loose numerical attachment;
it is the four-card structural source read through matrix, source-law, and
input-surface coordinates.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Four-card / matrix / source-law equality -/

/-- THEOREM 1: the closed four-card CKM/Jarlskog depth is exactly the
matrix-level Jarlskog depth. -/
theorem ckmJarlskogFourCardClosedDepthSum_eq_matrixDepth :
    ckmJarlskogFourCardClosedDepthSum = ckmJarlskogDepthFromMatrix := by
  rw [ckmJarlskogFourCardClosedDepthSum_eq_386,
    ckmJarlskogDepthFromMatrix_eq_386]
  norm_num [ckmCPDepthSum]

/-- THEOREM 2: the closed four-card depth and the matrix-level depth agree
after rational readout. -/
theorem ckmJarlskogFourCardClosedDepthSum_rat_eq_matrixDepth :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) =
      (ckmJarlskogDepthFromMatrix : ℚ) := by
  exact_mod_cast ckmJarlskogFourCardClosedDepthSum_eq_matrixDepth

/-- THEOREM 3: the full-beta-vector source-law sector gap is the same
four-card structural depth. -/
theorem sourceLawCKMDepthCoefficient_eq_fourCardClosedDepth :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
      (ckmJarlskogFourCardClosedDepthSum : ℚ) := by
  calc
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
        (ckmJarlskogDepthFromMatrix : ℚ) :=
      sourceLawCKMDepthCoefficient_eq_matrixDepth
    _ = (ckmJarlskogFourCardClosedDepthSum : ℚ) :=
      ckmJarlskogFourCardClosedDepthSum_rat_eq_matrixDepth.symm

/-- THEOREM 4: the four-card structural depth times exact running sigma gives
the raw CKM phase. -/
theorem fourCardCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  rw [ckmJarlskogFourCardClosedDepthSum_rat_eq_matrixDepth]
  exact ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim

/-! ## Four-card running-sigma equation -/

/-- The CKM running-sigma equation read directly from the four-card structural
depth. -/
def CKMFourCardRunningSigmaSolution (σ : ℚ) : Prop :=
  (ckmJarlskogFourCardClosedDepthSum : ℚ) * σ = cpRawPhaseClaim ℚ

/-- THEOREM 5: the four-card structural phase equation uniquely selects the
exact running sigma. -/
theorem ckmFourCardRunningSigmaSolution_iff_exact (σ : ℚ) :
    CKMFourCardRunningSigmaSolution σ ↔
      σ = sigmaGUTTwoLoopExact ℚ := by
  unfold CKMFourCardRunningSigmaSolution
  rw [ckmJarlskogFourCardClosedDepthSum_rat_eq_matrixDepth]
  exact ckmMatrixRunningSigmaSolution_iff_exact σ

/-- THEOREM 6: exact running sigma solves the four-card CKM phase equation. -/
theorem sigmaGUTTwoLoopExact_solves_fourCardCKMPhase :
    CKMFourCardRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ) :=
  (ckmFourCardRunningSigmaSolution_iff_exact
    (sigmaGUTTwoLoopExact ℚ)).mpr rfl

/-- THEOREM 7: nominal `13/1000` is not the four-card CKM phase solution. -/
theorem sigmaGUTNominal_not_fourCardCKMPhase_solution :
    ¬ CKMFourCardRunningSigmaSolution (sigmaGUTNominal ℚ) := by
  intro h
  have hsigma :=
    (ckmFourCardRunningSigmaSolution_iff_exact
      (sigmaGUTNominal ℚ)).mp h
  norm_num [sigmaGUTNominal, sigmaGUTTwoLoopExact] at hsigma

/-- THEOREM 8: rounded decimal proxy `0.01328 = 83/6250` is not the four-card
CKM phase solution. -/
theorem sigmaGUTTwoLoopDecimalProxy_not_fourCardCKMPhase_solution :
    ¬ CKMFourCardRunningSigmaSolution
        (sigmaGUTTwoLoopDecimalProxy ℚ) := by
  intro h
  have hsigma :=
    (ckmFourCardRunningSigmaSolution_iff_exact
      (sigmaGUTTwoLoopDecimalProxy ℚ)).mp h
  norm_num [sigmaGUTTwoLoopDecimalProxy, sigmaGUTTwoLoopExact] at hsigma

/-! ## Input-surface no-free readout -/

/-- THEOREM 9: every accepted full-beta-vector input surface reads the same
four-card structural CKM depth. -/
theorem inputSurfaceCKMDepth_eq_fourCardClosedDepth
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 =
      ckmJarlskogFourCardClosedDepthSum := by
  calc
    ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int) :=
      fullBetaVectorInputThreeNailSurfaceCertificate.ckm_jarlskog_sum C hC
    _ = ckmJarlskogFourCardClosedDepthSum := by
      rw [ckmJarlskogFourCardClosedDepthSum_eq_386]
      norm_num [ckmCPDepthSum]

/-- THEOREM 10: every accepted full-beta-vector input surface also carries the
same four typed Jarlskog factor contributions. -/
theorem inputSurfaceCKMJarlskogFactors_forced
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    CKMJarlskogFactor.depthContribution C.2 .V_us = (-226 : Int) ∧
      CKMJarlskogFactor.depthContribution C.2 .V_cb = (-143 : Int) ∧
        CKMJarlskogFactor.depthContribution C.2 .V_ub_conj = (562 : Int) ∧
          CKMJarlskogFactor.depthContribution C.2 .V_cs_conj = (193 : Int) :=
  (ckmPhaseProducerNormalForm_inputSurfaceMatrixPhase C hC).1

/-- THEOREM 11: the four-card sector-axis source surface is a singleton. -/
theorem ckmFourCardSourceSurface_eq_canonical
    (P : CKMSectorAxisPrimitiveCardPacket)
    (hP : CKMSectorAxisPrimitiveCardSourceEquations P) :
    P = canonicalCKMSectorAxisPrimitiveCardPacket :=
  eq_canonicalCKMSectorAxisPrimitiveCardPacket_of_sourceEquations P hP

/-! ## Bundled no-free structural certificate -/

/-- One certificate saying the CKM/Jarlskog phase-depth nail is the singleton
four-card source, read equivalently as the matrix Jarlskog depth, the source-law
sector gap, and the accepted input-surface factor quartet. -/
structure CKMJarlskogNoFreeStructuralSourceCertificate : Prop where
  four_card_closed_formula :
    Nonempty CKMJarlskogFourCardClosedFormulaProducerCertificate
  ckm_phase_source_normal_form :
    CKMPhaseProducerSourceNormalFormCertificate
  grand_concrete_source_normal_form :
    GrandUnification.GrandConcreteProducerNumericalSourceNormalFormCertificate
  source_surface_singleton :
    ∀ P : CKMSectorAxisPrimitiveCardPacket,
      CKMSectorAxisPrimitiveCardSourceEquations P ->
        P = canonicalCKMSectorAxisPrimitiveCardPacket
  four_card_eq_matrix :
    ckmJarlskogFourCardClosedDepthSum = ckmJarlskogDepthFromMatrix
  four_card_rat_eq_matrix :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) =
      (ckmJarlskogDepthFromMatrix : ℚ)
  source_law_eq_four_card :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis =
      (ckmJarlskogFourCardClosedDepthSum : ℚ)
  exact_raw_phase :
    (ckmJarlskogFourCardClosedDepthSum : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ
  solution_iff_exact :
    ∀ σ : ℚ,
      CKMFourCardRunningSigmaSolution σ ↔
        σ = sigmaGUTTwoLoopExact ℚ
  exact_solves :
    CKMFourCardRunningSigmaSolution (sigmaGUTTwoLoopExact ℚ)
  nominal_rejected :
    ¬ CKMFourCardRunningSigmaSolution (sigmaGUTNominal ℚ)
  decimal_proxy_rejected :
    ¬ CKMFourCardRunningSigmaSolution
        (sigmaGUTTwoLoopDecimalProxy ℚ)
  input_surface_depth :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 =
          ckmJarlskogFourCardClosedDepthSum
  input_surface_factors :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        CKMJarlskogFactor.depthContribution C.2 .V_us = (-226 : Int) ∧
          CKMJarlskogFactor.depthContribution C.2 .V_cb = (-143 : Int) ∧
            CKMJarlskogFactor.depthContribution C.2 .V_ub_conj =
                (562 : Int) ∧
              CKMJarlskogFactor.depthContribution C.2 .V_cs_conj =
                (193 : Int)

/-- THEOREM 12: CKM/Jarlskog no-free structural source certificate. -/
theorem ckmJarlskogNoFreeStructuralSourceCertificate :
    CKMJarlskogNoFreeStructuralSourceCertificate where
  four_card_closed_formula :=
    ⟨ckmJarlskogFourCardClosedFormulaProducerCertificate⟩
  ckm_phase_source_normal_form :=
    ckmPhaseProducerSourceNormalFormCertificate
  grand_concrete_source_normal_form :=
    GrandUnification.grandConcreteProducerNumericalSourceNormalFormCertificate
  source_surface_singleton :=
    ckmFourCardSourceSurface_eq_canonical
  four_card_eq_matrix :=
    ckmJarlskogFourCardClosedDepthSum_eq_matrixDepth
  four_card_rat_eq_matrix :=
    ckmJarlskogFourCardClosedDepthSum_rat_eq_matrixDepth
  source_law_eq_four_card :=
    sourceLawCKMDepthCoefficient_eq_fourCardClosedDepth
  exact_raw_phase :=
    fourCardCKMDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
  solution_iff_exact :=
    ckmFourCardRunningSigmaSolution_iff_exact
  exact_solves :=
    sigmaGUTTwoLoopExact_solves_fourCardCKMPhase
  nominal_rejected :=
    sigmaGUTNominal_not_fourCardCKMPhase_solution
  decimal_proxy_rejected :=
    sigmaGUTTwoLoopDecimalProxy_not_fourCardCKMPhase_solution
  input_surface_depth :=
    inputSurfaceCKMDepth_eq_fourCardClosedDepth
  input_surface_factors :=
    inputSurfaceCKMJarlskogFactors_forced

end StandardModelConstraint
end SaturationMonoid
