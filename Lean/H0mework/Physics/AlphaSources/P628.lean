import H0mework.Realization.Relations.P620
import H0mework.Physics.AlphaSources.P627

/-!
# Proposition 628: current finite core upgraded to the unified alpha_s axis

P620 is the current finite/projection-level root, but its three-nail receipt
still cites the earlier P618 alpha_s producer.  P627 proved the stronger
finite alpha_s nail: the same QCD/Poincare axis

`b0_QCD + slots_4D = 7 + 3 = 10`

reconstructs the visible-gauge offset, electromagnetic denominator,
SU(7)-breaking numerator, finite denominator, alpha-gap, and inverse residual.

This file reconnects that stronger P627 alpha_s nail to the current unified
finite root, while keeping the already checked Yukawa depth table and CKM
depth-sum nails from P619/P620.

Boundary: this is a root/receipt upgrade, not a new smooth-dynamics producer.
The remaining physical producer debt is still threshold / three-loop RG /
Higgs-extra dynamics and independent real GUT-scale Yukawa extraction.
-/

noncomputable section

namespace SaturationMonoid

open StandardModelConstraint

/-! ## Three-nail receipt with the P627 alpha_s nail -/

/-- The current three-nail receipt with the alpha_s nail upgraded from the
older P618 finite-geometry producer to the P627 unified QCD/Poincare-axis
producer. -/
structure UnifiedAxisProducerDebtThreeNailReceipt where
  alpha_s_unified_axis :
    AlphaStrongQCDPoincareUnifiedAxisProducerReceipt
  yukawa_primitive_cards :
    YukawaPrimitiveCardProducerReceipt
  yukawa_generated_table :
    YukawaDepthTableGeneratedSingletonReceipt
  yukawa_coefficient_no_choice :
    YukawaCarrierCoefficientNoChoiceReceipt
  ckm_sector_axis :
    CKMSectorAxisPrimitiveCardProducerReceipt
  alpha_axis :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ)
  alpha_visible_gauge :
    alphaStrongQCDPoincareVisibleGaugeFromAxis = (9 : ℚ)
  alpha_em_denominator :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator = (137 : ℚ)
  alpha_numerator :
    alphaStrongQCDPoincareUnifiedAxisNumerator = (89 : ℚ)
  alpha_denominator :
    alphaStrongQCDPoincareResolutionDenominator = (10000 : ℚ)
  alpha_gap :
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate.gap =
      (89 : ℚ) / 10000
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  alpha_displayed_closure :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ
  yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ)

/-- THEOREM 1: the upgraded three-nail receipt is inhabited. -/
theorem unifiedAxisProducerDebtThreeNailReceipt :
    UnifiedAxisProducerDebtThreeNailReceipt where
  alpha_s_unified_axis :=
    alphaStrongQCDPoincareUnifiedAxisProducerReceipt
  yukawa_primitive_cards := yukawaPrimitiveCardProducerReceipt
  yukawa_generated_table := yukawaDepthTableGeneratedSingletonReceipt
  yukawa_coefficient_no_choice := yukawaCarrierCoefficientNoChoiceReceipt
  ckm_sector_axis := ckmSectorAxisPrimitiveCardProducerReceipt
  alpha_axis := alphaStrongQCDPoincareResolutionAxis_eq_ten
  alpha_visible_gauge :=
    alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine
  alpha_em_denominator :=
    alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_137
  alpha_numerator :=
    alphaStrongQCDPoincareUnifiedAxisNumerator_eq_89
  alpha_denominator :=
    alphaStrongQCDPoincareResolutionDenominator_eq_10000
  alpha_gap :=
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_gap
  alpha_inverse_residual :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection
  alpha_displayed_closure :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_closes_displayedAlpha
  yukawa_depths :=
    primitiveCardYukawaProducerInputCandidate_massOrder_eq
  ckm_depth_sum :=
    canonicalCKMSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386

/-! ## Current unified finite root with the stronger alpha_s nail -/

/-- Current unified finite core whose alpha_s witness is the P627 unified-axis
producer rather than the older P618 finite-geometry producer. -/
structure CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate where
  previous_finite_core :
    CurrentUnifiedEquationFiniteCoreCertificate
  unified_axis_alpha_s_core :
    CurrentUnifiedEquationAlphaStrongUnifiedAxisCoreCertificate
  unified_axis_three_nails :
    UnifiedAxisProducerDebtThreeNailReceipt
  alpha_s_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ)
  alpha_displayed_closure :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 2: the current unified finite root upgraded to the P627 alpha_s
axis is inhabited. -/
def currentUnifiedEquationUnifiedAxisFiniteCoreCertificate :
    CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate where
  previous_finite_core := currentUnifiedEquationFiniteCoreCertificate
  unified_axis_alpha_s_core :=
    currentUnifiedEquationAlphaStrongUnifiedAxisCoreCertificate
  unified_axis_three_nails := unifiedAxisProducerDebtThreeNailReceipt
  alpha_s_residual :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection
  yukawa_depths :=
    unifiedAxisProducerDebtThreeNailReceipt.yukawa_depths
  ckm_depth_sum :=
    unifiedAxisProducerDebtThreeNailReceipt.ckm_depth_sum
  alpha_displayed_closure :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_closes_displayedAlpha

namespace CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate

/-- THEOREM 3: the upgraded root exposes the P627 exact alpha_s inverse
residual. -/
theorem alpha_s_residual_eq
    (C : CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) :=
  C.alpha_s_residual

/-- THEOREM 4: the upgraded root still exposes the generated Yukawa depth
table. -/
theorem yukawa_depth_table
    (C : CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate) :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  C.yukawa_depths

/-- THEOREM 5: the upgraded root still exposes the finite CKM/Jarlskog
sector-axis depth sum. -/
theorem ckm_depth_sum_eq_386
    (C : CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate) :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ) :=
  C.ckm_depth_sum

/-- THEOREM 6: the upgraded root closes displayed `alpha_s` using the P627
unified-axis producer. -/
theorem alpha_s_displayed_closure
    (C : CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ :=
  C.alpha_displayed_closure

/-- THEOREM 7: the canonical upgraded root still carries the original P620
formula-level coordinate-action spine. -/
theorem canonical_previous_coordinate_core :
    currentUnifiedEquationUnifiedAxisFiniteCoreCertificate.previous_finite_core =
      currentUnifiedEquationFiniteCoreCertificate := by
  rfl

end CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate

end SaturationMonoid
