import H0mework.Physics.AlphaSources.P600
import H0mework.Physics.JointSources.P523
import H0mework.Physics.JointSources.P664

/-!
# Proposition 665: alpha_s producer-pressure strengthening of the central root

P664 is the strongest central root for the current finite form of
`information = mathematics = matter = energy`.

This file welds the alpha_s producer-pressure chain onto that root:

* P600 gives the finite carrier arithmetic directly:
  `128`, `137`, `89`, `10`, `10000`, hence the gap `89/10000` and inverse
  correction `-89000/128511`;
* P521 proves that the same alpha-level gap is strict positive residual debt:
  any successful four-source physical residual producer must have a positive
  source contribution;
* P523 ties that residual necessity to the current concrete SU7
  representation-physicalization receipt.

Boundary: this still does not calculate the smooth threshold / three-loop RG /
Higgs-extra spectrum.  It proves that the finite central root, direct carrier
arithmetic, and physical residual-necessity law are the same pressure point.
-/

noncomputable section

namespace SaturationMonoid

universe u

namespace GrandUnification

open StandardModelConstraint

/-- The central root strengthened by the alpha_s producer-pressure receipt.

The important new invariant is not another decimal equality.  It is the
coincidence of three layers:

1. finite typed carrier arithmetic gives the alpha gap;
2. the QCD / two-loop comparison says this gap is strict producer debt;
3. the SU7 representation-physicalization receipt carries that necessity.
-/
structure AlphaStrongProducerPressureUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  refined_central_root :
    RefinedInformationMathMatterEnergyUnifiedRootCertificate E
  finite_carrier :
    AlphaStrongFiniteCarrierGapProducerReceipt
  representation_physicalization :
    SU7RepresentationPhysicalizationReceipt
  residual_necessity :
    AlphaStrongResidualNecessityReceipt
  finite_carrier_gap_matches_residual_gap :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      alphaStrongTwoLoopSMDisplayedGap ℚ
  direct_carrier_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      -((89000 : ℚ) / 128511)
  current_physical_alpha_is_canonical_su7 :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongSU7BreakingResidualGapProducer
  current_physical_alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  qcd_beta_7 :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7
  residual_gap_positive :
    0 < alphaStrongTwoLoopSMDisplayedGap ℚ
  every_successful_residual_producer_has_positive_source :
    ∀ P : AlphaStrongResidualGapProducer,
      ∃ s : AlphaStrongResidualSource, 0 < P.contribution s
  finite_layer_su7_source_gap :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking =
      (89 : ℚ) / 10000
  finite_layer_non_su7_sources_zero :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threshold = 0 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threeLoopRG = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .higgsExtraRepresentation = 0

/-- THEOREM 1: the alpha_s producer-pressure strengthened central root is
inhabited. -/
def alphaStrongProducerPressureUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    AlphaStrongProducerPressureUnifiedRootCertificate E where
  refined_central_root :=
    refinedInformationMathMatterEnergyUnifiedRootCertificate (E := E)
  finite_carrier := alphaStrongFiniteCarrierGapProducerReceipt
  representation_physicalization := su7RepresentationPhysicalizationReceipt
  residual_necessity := alphaStrongResidualNecessityReceipt
  finite_carrier_gap_matches_residual_gap := by
    rw [finiteCarrierAlphaStrongSU7BreakingGapCandidate_gap,
      alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  direct_carrier_inverse_residual :=
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_inverseCorrection_direct
  current_physical_alpha_is_canonical_su7 :=
    refinedCentralRoot_alpha_physical_object_canonical (E := E)
  current_physical_alpha_inverse_residual :=
    refinedCentralRoot_alpha_inverse_residual (E := E)
  qcd_beta_7 := RunningSigmaBeta.qcdCarrierB0FinalReceipt.beta_formula
  residual_gap_positive := alphaStrongTwoLoopSMDisplayedGap_pos
  every_successful_residual_producer_has_positive_source :=
    fun P => P.exists_positive_source
  finite_layer_su7_source_gap :=
    unifiedFiniteThreeNailClosureCertificate.finite_alpha_su7_source_gap
  finite_layer_non_su7_sources_zero :=
    unifiedFiniteThreeNailClosureCertificate.finite_alpha_non_su7_sources_zero

/-! ## Focused projections -/

/-- THEOREM 2: the finite carrier gap is the same alpha-level residual gap
left by the two-loop Standard-Model output. -/
theorem alphaStrongProducerPressure_finite_gap_matches_residual_gap
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      alphaStrongTwoLoopSMDisplayedGap ℚ :=
  (alphaStrongProducerPressureUnifiedRootCertificate
    (E := E)).finite_carrier_gap_matches_residual_gap

/-- THEOREM 3: the strengthened root exposes the direct finite-carrier inverse
correction, without using a displayed-output target as an intermediate. -/
theorem alphaStrongProducerPressure_direct_carrier_inverse_residual
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      -((89000 : ℚ) / 128511) :=
  (alphaStrongProducerPressureUnifiedRootCertificate
    (E := E)).direct_carrier_inverse_residual

/-- THEOREM 4: the strengthened root keeps the current physical alpha object
identified with the canonical SU7 finite producer. -/
theorem alphaStrongProducerPressure_current_alpha_canonical
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongSU7BreakingResidualGapProducer :=
  (alphaStrongProducerPressureUnifiedRootCertificate
    (E := E)).current_physical_alpha_is_canonical_su7

/-- THEOREM 5: the strengthened root exposes the positive-source necessity
for every successful four-source alpha_s residual producer. -/
theorem alphaStrongProducerPressure_positive_source_necessity
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (P : AlphaStrongResidualGapProducer) :
    ∃ s : AlphaStrongResidualSource, 0 < P.contribution s :=
  (alphaStrongProducerPressureUnifiedRootCertificate
    (E := E)).every_successful_residual_producer_has_positive_source P

/-- THEOREM 6: on the current finite layer, the alpha_s residual is entirely
on the SU7-breaking source and the other three sources are zero. -/
theorem alphaStrongProducerPressure_finite_source_normal_form
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking = (89 : ℚ) / 10000 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .threshold = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .threeLoopRG = 0 ∧
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
              .higgsExtraRepresentation = 0 :=
  ⟨(alphaStrongProducerPressureUnifiedRootCertificate
      (E := E)).finite_layer_su7_source_gap,
    (alphaStrongProducerPressureUnifiedRootCertificate
      (E := E)).finite_layer_non_su7_sources_zero⟩

end GrandUnification
end SaturationMonoid
