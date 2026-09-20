import H0mework.Physics.SourceForms.P781
import H0mework.Physics.AlphaSources.P786

/-!
# Proposition 787: concrete three-nail producer identity spine

P781 packages the concrete alpha/Yukawa/CKM numerical producer spine.
P786 strengthens the alpha leg: the independently computed
`SU(7) breaking / threshold / RG / Higgs-extra` receipt is exactly the
canonical four-source receipt and the unified-axis alpha producer.

This file fuses those two facts at the accepted input surface.  An accepted
three-nail input no longer merely emits the same scalar values; its alpha leg
is the independent four-source receipt, its Yukawa leg is the primitive-card
endpoint schedule, and its CKM leg is the four-card structural source.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open StandardModelConstraint

/-! ## Accepted input surface as one identity spine -/

/-- THEOREM 1: every accepted input-surface alpha gap is the produced gap of
the independent four-source alpha receipt from P785/P786. -/
theorem inputSurface_alphaGap_eq_independentFourSourceReceipt
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.1.producedGap =
      alphaStrongIndependentFourSourceReceipt.toGapProducer.producedGap := by
  calc
    C.1.producedGap =
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap := by
          exact inputSurface_alphaGap_eq_unifiedAxisProducedGap C hC
    _ = alphaStrongIndependentFourSourceReceipt.toGapProducer.producedGap := by
          exact
            (congrArg AlphaStrongResidualGapProducer.producedGap
              alphaStrongIndependentFourSourceReceipt_toGapProducer_eq_unifiedAxis).symm

/-- THEOREM 2: the independent four-source receipt transports to the exact
inverse residual in its own producer coordinate. -/
theorem alphaStrongIndependentFourSourceReceipt_producedGap_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongIndependentFourSourceReceipt.toGapProducer.producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [AlphaStrongResidualGapProducer.producedGap_eq_univ_sum]
  exact alphaStrongIndependentFourSourceReceipt_inverseResidual

/-- THEOREM 3: every accepted input-surface alpha residual is the same
independent four-source residual. -/
theorem inputSurface_alphaResidual_eq_independentFourSourceReceipt
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.1.producedGap =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongIndependentFourSourceReceipt.toGapProducer.producedGap := by
  rw [inputSurface_alphaGap_eq_independentFourSourceReceipt C hC]

/-- THEOREM 4: every accepted input-surface Yukawa table is the primitive-card
coefficient endpoint schedule. -/
theorem inputSurface_yukawaTable_eq_primitiveEndpointSchedule
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2 =
      coefficientScheduleYukawaDepthTableCandidate
        (primitiveCardYukawaDepthStencilCoefficientVector
          canonicalYukawaCoefficientPrimitiveCardPacket)
        yukawaSectorInformationIncidence :=
  inputSurface_yukawaTable_eq_canonicalCoefficientEndpointSchedule C hC

/-- THEOREM 5: every accepted input-surface CKM four-product depth is the
closed four-card structural depth. -/
theorem inputSurface_ckmDepth_eq_fourCardClosedDepth
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 =
      ckmJarlskogFourCardClosedDepthSum :=
  inputSurfaceCKMDepth_eq_fourCardClosedDepth C hC

/-- THEOREM 6: every accepted input-surface CKM raw phase is the four-card
structural raw phase. -/
theorem inputSurface_ckmRawPhase_eq_fourCardClosedDepth
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
        sigmaGUTTwoLoopExact ℚ =
      (ckmJarlskogFourCardClosedDepthSum : ℚ) *
        sigmaGUTTwoLoopExact ℚ := by
  rw [inputSurface_ckmDepth_eq_fourCardClosedDepth C hC]

/-! ## Bundled identity-spine certificate -/

/-- One certificate saying the concrete numerical producer chain has a single
input-surface identity spine:

* alpha is the independent four-source receipt;
* Yukawa is the primitive-card endpoint schedule;
* CKM/Jarlskog is the closed four-card structural source;
* the same roof also carries the representation/matter/Higgs and leave-one-out
  producer normal forms.
-/
structure ConcreteThreeNailProducerIdentitySpineCertificate : Prop where
  roof :
    GrandConcreteProducerNumericalSourceNormalFormCertificate
  alpha_four_source_identity :
    AlphaStrongFourSourceIdentityProducerCertificate
  yukawa_depth_source_normal_form :
    YukawaDepthProducerSourceNormalFormCertificate
  yukawa_leave_one_out :
    Nonempty (YukawaLeaveOneOutSourceNormalFormCertificate ℂ)
  ckm_no_free_structural_source :
    CKMJarlskogNoFreeStructuralSourceCertificate
  su7_representation_matter_higgs :
    SU7RepresentationMatterHiggsSourceNormalFormCertificate
  alpha_receipt_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongIndependentFourSourceReceipt.toGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  input_alpha_receipt :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.1.producedGap =
          alphaStrongIndependentFourSourceReceipt.toGapProducer.producedGap
  input_alpha_receipt_residual :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap =
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongIndependentFourSourceReceipt.toGapProducer.producedGap
  input_yukawa_endpoint_schedule :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2 =
          coefficientScheduleYukawaDepthTableCandidate
            (primitiveCardYukawaDepthStencilCoefficientVector
              canonicalYukawaCoefficientPrimitiveCardPacket)
            yukawaSectorInformationIncidence
  input_ckm_four_card :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 =
          ckmJarlskogFourCardClosedDepthSum
  input_ckm_four_card_raw_phase :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        (ckmJarlskogFourProductDepthSum C.2 : ℚ) *
            sigmaGUTTwoLoopExact ℚ =
          (ckmJarlskogFourCardClosedDepthSum : ℚ) *
            sigmaGUTTwoLoopExact ℚ

/-- THEOREM 7: concrete three-nail producer identity-spine certificate. -/
theorem concreteThreeNailProducerIdentitySpineCertificate :
    ConcreteThreeNailProducerIdentitySpineCertificate where
  roof :=
    grandConcreteProducerNumericalSourceNormalFormCertificate
  alpha_four_source_identity :=
    alphaStrongFourSourceIdentityProducerCertificate
  yukawa_depth_source_normal_form :=
    yukawaDepthProducerSourceNormalFormCertificate
  yukawa_leave_one_out :=
    ⟨yukawaLeaveOneOutSourceNormalFormCertificate (E := ℂ)⟩
  ckm_no_free_structural_source :=
    ckmJarlskogNoFreeStructuralSourceCertificate
  su7_representation_matter_higgs :=
    su7RepresentationMatterHiggsSourceNormalFormCertificate
  alpha_receipt_inverse_residual :=
    alphaStrongIndependentFourSourceReceipt_producedGap_inverseResidual
  input_alpha_receipt :=
    inputSurface_alphaGap_eq_independentFourSourceReceipt
  input_alpha_receipt_residual :=
    inputSurface_alphaResidual_eq_independentFourSourceReceipt
  input_yukawa_endpoint_schedule :=
    inputSurface_yukawaTable_eq_primitiveEndpointSchedule
  input_ckm_four_card :=
    inputSurface_ckmDepth_eq_fourCardClosedDepth
  input_ckm_four_card_raw_phase :=
    inputSurface_ckmRawPhase_eq_fourCardClosedDepth

end GrandUnification
end SaturationMonoid
