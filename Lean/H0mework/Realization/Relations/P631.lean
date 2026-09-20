import H0mework.Physics.YukawaSources.P630

/-!
# Proposition 631: one-axis finite producer core

P627 routes `alpha_s` through the QCD/Poincare axis.
P629 routes the CKM/Jarlskog sector sum through that same axis.
P630 routes the Yukawa coefficient surface and selected `3 x 3` depth grid
through that same axis.

This file packages the current strongest finite/projection-level result:
one shared finite axis exposes all three producer nails:

* `alpha_s` inverse residual `-89000/128511`;
* Yukawa mass-order depths `[50,346,372,489,583,682,880,908,982]`;
* CKM/Jarlskog depth sum `386`.

Boundary: this is still a finite-cardinality producer core.  It does not
construct smooth SU(7) breaking, threshold spectra, three-loop RG, Higgs-extra
representation dynamics, or a full CKM matrix.
-/

noncomputable section

namespace SaturationMonoid

open StandardModelConstraint

/-- Current one-axis finite producer core: the same QCD/Poincare axis now
drives the finite alpha_s, Yukawa-grid, and CKM/Jarlskog receipts. -/
structure CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate where
  previous_axis_ckm_core :
    CurrentUnifiedEquationUnifiedAxisCKMCoreCertificate
  alpha_s_axis_receipt :
    AlphaStrongQCDPoincareUnifiedAxisProducerReceipt
  yukawa_axis_receipt :
    QCDPoincareUnifiedAxisYukawaProducerReceipt
  ckm_axis_receipt :
    QCDPoincareUnifiedAxisCKMProducerReceipt
  shared_axis :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ)
  axis_visible_gauge :
    alphaStrongQCDPoincareVisibleGaugeFromAxis = (9 : ℚ)
  axis_alpha_em :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator = (137 : ℚ)
  alpha_s_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  alpha_s_displayed_closure :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ
  yukawa_grid :
    qcdPoincareUnifiedAxisYukawaDepthGrid = selectedYukawaDepthGrid
  yukawa_mass_order :
    rationalGridMassOrder qcdPoincareUnifiedAxisYukawaDepthGrid =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  yukawa_jarlskog :
    ckmJarlskogDepthSumFromRationalGrid
        qcdPoincareUnifiedAxisYukawaDepthGrid =
      (386 : ℚ)
  ckm_sector_gap :
    qcdPoincareUnifiedAxisCKMSectorGap = (193 : ℚ)
  ckm_depth_sum_from_axis :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ)

/-- THEOREM 1: the strongest current finite core is inhabited. -/
def currentUnifiedEquationOneAxisFiniteProducerCoreCertificate :
    CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate where
  previous_axis_ckm_core :=
    currentUnifiedEquationUnifiedAxisCKMCoreCertificate
  alpha_s_axis_receipt :=
    alphaStrongQCDPoincareUnifiedAxisProducerReceipt
  yukawa_axis_receipt :=
    qcdPoincareUnifiedAxisYukawaProducerReceipt
  ckm_axis_receipt :=
    qcdPoincareUnifiedAxisCKMProducerReceipt
  shared_axis := alphaStrongQCDPoincareResolutionAxis_eq_ten
  axis_visible_gauge :=
    alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine
  axis_alpha_em :=
    alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_137
  alpha_s_residual :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection
  alpha_s_displayed_closure :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_closes_displayedAlpha
  yukawa_grid := qcdPoincareUnifiedAxisYukawaDepthGrid_eq_selected
  yukawa_mass_order :=
    qcdPoincareUnifiedAxisYukawaDepthGrid_massOrder_eq
  yukawa_jarlskog :=
    qcdPoincareUnifiedAxisYukawaDepthGrid_jarlskogDepthSum_eq_386
  ckm_sector_gap := qcdPoincareUnifiedAxisCKMSectorGap_eq_193
  ckm_depth_sum_from_axis :=
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386

namespace CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate

/-- THEOREM 2: the one-axis core exposes the exact alpha_s inverse residual. -/
theorem alpha_s_residual_eq
    (C : CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) :=
  C.alpha_s_residual

/-- THEOREM 3: the one-axis core exposes the Yukawa depth mass-order list. -/
theorem yukawa_mass_order_eq
    (C : CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate) :
    rationalGridMassOrder qcdPoincareUnifiedAxisYukawaDepthGrid =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  C.yukawa_mass_order

/-- THEOREM 4: the one-axis Yukawa grid already carries the Jarlskog depth
sum `386`. -/
theorem yukawa_jarlskog_eq_386
    (C : CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate) :
    ckmJarlskogDepthSumFromRationalGrid
        qcdPoincareUnifiedAxisYukawaDepthGrid =
      (386 : ℚ) :=
  C.yukawa_jarlskog

/-- THEOREM 5: the independent CKM sector-axis receipt also gives the same
Jarlskog depth sum `386`. -/
theorem ckm_depth_sum_from_axis_eq_386
    (C : CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate) :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ) :=
  C.ckm_depth_sum_from_axis

/-- THEOREM 6: the one-axis core exposes the shared finite axis itself. -/
theorem shared_axis_eq_ten
    (C : CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate) :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ) :=
  C.shared_axis

end CurrentUnifiedEquationOneAxisFiniteProducerCoreCertificate

end SaturationMonoid
