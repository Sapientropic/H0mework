import H0mework.Physics.JointSources.P605
import H0mework.Physics.MixingSources.P649

/-!
# Proposition 650: unified finite three-nail closure

P647, P648, and P649 close the three current producer-debt nails separately:

* `alpha_s`: the finite QCD/Poincare unified-axis producer is the canonical
  SU7-only finite producer and carries inverse residual `-89000/128511`;
* Yukawa depths: primitive finite-card equations plus an endpoint-preserving
  SU7 sector schedule force the nine integer depths;
* CKM/Jarlskog: the same producer surface forces the four typed Jarlskog
  factors and depth sum `386`.

P605 is the older main receipt connecting these outputs to the gauge core,
information/matter core, 4D Poincare-resolution alpha producer, and
primitive-card Yukawa producer.

This file packages those two views into one root certificate.  It adds no new
physics mechanism; it removes the remaining bookkeeping split between the main
receipt and the three refined producer-debt closure certificates.

Boundary: this is still finite-card / current-formal-geometry closure.  It is
not a smooth SU7-breaking dynamics, threshold spectrum, three-loop RG,
Higgs-extra representation, full CKM matrix, or low-energy fidelity proof.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Current finite three-nail root certificate -/

/-- One root certificate for the current finite Standard-Model producer line.

The certificate carries:

* the P605 main-nails receipt;
* the P646 one-axis upstream finite source;
* the P647 alpha_s finite producer closure;
* the P648 Yukawa finite depth closure;
* the P649 CKM/Jarlskog finite phase-depth closure.

The displayed output fields are duplicated intentionally so downstream files can
use this as a single entrypoint without reopening the internal receipt chain. -/
structure UnifiedFiniteThreeNailClosureCertificate where
  main_nails :
    MainProducerNailsCertificate
      currentFormalFourDPoincareCertificate
      unifiedGaugeIntoAlphaEMStructural
  one_axis_three_nail :
    OneAxisPrimitiveSourceThreeNailProducerCertificate
      canonicalOneAxisPrimitiveSourceProducer
  alpha_s_finite :
    AlphaStrongFiniteProducerDebtClosureCertificate
  yukawa_finite :
    YukawaFiniteDepthProducerDebtClosureCertificate
  ckm_finite :
    CKMFiniteJarlskogProducerDebtClosureCertificate
  main_alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPoincareResolutionResidualGapProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  finite_alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  finite_alpha_su7_source_gap :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking =
      (89 : ℚ) / 10000
  finite_alpha_non_su7_sources_zero :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threshold = 0 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threeLoopRG = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .higgsExtraRepresentation = 0
  yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_factors_on_forced_surface :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              CKMJarlskogFactor.depthContribution T .V_us = (-226 : Int) ∧
                CKMJarlskogFactor.depthContribution T .V_cb = (-143 : Int) ∧
                  CKMJarlskogFactor.depthContribution T .V_ub_conj = (562 : Int) ∧
                    CKMJarlskogFactor.depthContribution T .V_cs_conj = (193 : Int)
  ckm_depth_sum_on_forced_surface :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot)
      (T : YukawaDepthTableCandidate),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            T =
              coefficientScheduleYukawaDepthTableCandidate
                (primitiveCardYukawaDepthStencilCoefficientVector P) f ->
              ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int)
  ckm_expanded_sum :
    (-226 : Int) + (-143 : Int) + (562 : Int) + (193 : Int) =
      (ckmCPDepthSum : Int)

/-- THEOREM 1: current finite three-nail root closure certificate. -/
def unifiedFiniteThreeNailClosureCertificate :
    UnifiedFiniteThreeNailClosureCertificate where
  main_nails := canonicalCurrentFormalMainProducerNailsCertificate
  one_axis_three_nail :=
    canonicalOneAxisPrimitiveSourceThreeNailProducerCertificate
  alpha_s_finite := alphaStrongFiniteProducerDebtClosureCertificate
  yukawa_finite := yukawaFiniteDepthProducerDebtClosureCertificate
  ckm_finite := ckmFiniteJarlskogProducerDebtClosureCertificate
  main_alpha_inverse_residual :=
    MainProducerNailsCertificate.alpha_s_residual
      canonicalCurrentFormalMainProducerNailsCertificate
  finite_alpha_inverse_residual :=
    alphaStrongFiniteProducerDebtClosureCertificate.alpha_inverse_residual
  finite_alpha_su7_source_gap :=
    alphaStrongFiniteProducerDebtClosureCertificate.su7_source_gap
  finite_alpha_non_su7_sources_zero :=
    alphaStrongFiniteProducerDebtClosureCertificate.non_su7_sources_zero
  yukawa_depths := primitiveCardYukawaProducerInputCandidate_massOrder_eq
  ckm_factors_on_forced_surface :=
    ckmFiniteJarlskogProducerDebtClosureCertificate.factors_forced
  ckm_depth_sum_on_forced_surface :=
    ckmFiniteJarlskogProducerDebtClosureCertificate.depth_sum_forced
  ckm_expanded_sum :=
    ckmFiniteJarlskogProducerDebtClosureCertificate.expanded_sum

/-! ## Lightweight projections from the root certificate -/

/-- THEOREM 2: the root certificate exposes the exact alpha_s inverse residual
on the main Poincare-resolution alpha producer. -/
theorem unifiedFiniteThreeNailClosure_alpha_s_main_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPoincareResolutionResidualGapProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511) :=
  unifiedFiniteThreeNailClosureCertificate.main_alpha_inverse_residual

/-- THEOREM 3: the root certificate exposes the exact alpha_s inverse residual
on the finite unified-axis producer. -/
theorem unifiedFiniteThreeNailClosure_alpha_s_finite_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) :=
  unifiedFiniteThreeNailClosureCertificate.finite_alpha_inverse_residual

/-- THEOREM 4: the root certificate exposes the nine forced Yukawa depths. -/
theorem unifiedFiniteThreeNailClosure_yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  unifiedFiniteThreeNailClosureCertificate.yukawa_depths

/-- THEOREM 5: the root certificate exposes the CKM/Jarlskog depth sum `386`
on every primitive-card / endpoint-ordering generated table. -/
theorem unifiedFiniteThreeNailClosure_ckm_depth_sum
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (T : YukawaDepthTableCandidate)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f)
    (hT :
      T =
        coefficientScheduleYukawaDepthTableCandidate
          (primitiveCardYukawaDepthStencilCoefficientVector P) f) :
    ckmJarlskogFourProductDepthSum T = (ckmCPDepthSum : Int) :=
  unifiedFiniteThreeNailClosureCertificate.ckm_depth_sum_on_forced_surface
    P f T hP hf hT

end StandardModelConstraint
end SaturationMonoid
