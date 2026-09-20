import H0mework.Physics.AlphaSources.P628

/-!
# Proposition 629: CKM sector axis from the unified QCD/Poincare axis

P617 proves that the CKM/Jarlskog depth sum `386` only needs the four-card
sector-axis packet:

`alphaDenominator = 137`, `visibleGauge = 9`,
`unifiedGaugeFreedom = 48`, `unit = 1`.

P627 has now reconstructed the first two cards from the same QCD/Poincare axis
used by the alpha_s residual producer:

`axis = b0_QCD + slots_4D = 10`,
`visible = axis - 1 = 9`,
`alphaDenominator = 2^7 + visible = 137`.

This file reconnects the CKM nail to that axis.  It proves that the
axis-derived sector gap is `193`, hence the typed Jarlskog four-product depth
sum is `2 * 193 = 386`.

Boundary: this is still a finite sector-axis producer.  It does not derive the
full CKM matrix or the continuous SU(7)-breaking dynamics selecting the whole
Yukawa depth grid.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## CKM sector gap from the shared QCD/Poincare axis -/

/-- The CKM-relevant sector-axis gap with its electromagnetic denominator and
visible-gauge term supplied by the P627 QCD/Poincare unified axis. -/
def qcdPoincareUnifiedAxisCKMSectorGap : ℚ :=
  (su7GaugeFreedomDimension ℚ - 1) -
    (-(alphaStrongQCDPoincareStructuralAlphaEMDenominator +
      alphaStrongQCDPoincareVisibleGaugeFromAxis))

/-- THEOREM 1: the P627 axis-derived CKM sector gap is the existing P616
sector-axis carrier gap. -/
theorem qcdPoincareUnifiedAxisCKMSectorGap_eq_rationalSectorAxisCarrierGap :
    qcdPoincareUnifiedAxisCKMSectorGap =
      rationalSectorAxisCarrierGap := by
  rw [qcdPoincareUnifiedAxisCKMSectorGap, rationalSectorAxisCarrierGap,
    alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_alphaEMIntegerDenominator,
    alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine,
    visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]
  norm_num

/-- THEOREM 2: the P627 axis-derived CKM sector gap is `193`. -/
theorem qcdPoincareUnifiedAxisCKMSectorGap_eq_193 :
    qcdPoincareUnifiedAxisCKMSectorGap = (193 : ℚ) := by
  rw [qcdPoincareUnifiedAxisCKMSectorGap_eq_rationalSectorAxisCarrierGap,
    rationalSectorAxisCarrierGap_eq_193]

/-- THEOREM 3: twice the P627 axis-derived sector gap is the CKM/Jarlskog
depth sum `386`. -/
theorem twice_qcdPoincareUnifiedAxisCKMSectorGap_eq_386 :
    2 * qcdPoincareUnifiedAxisCKMSectorGap = (386 : ℚ) := by
  rw [qcdPoincareUnifiedAxisCKMSectorGap_eq_193]
  norm_num

/-! ## Four-card packet whose first two cards are certified by P627 -/

/-- The CKM four-card packet read in the P627 unified-axis coordinates. -/
def qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket :
    CKMSectorAxisPrimitiveCardPacket where
  alphaDenominator := 137
  visibleGauge := 9
  unifiedGaugeFreedom := 48
  unit := 1

/-- THEOREM 4: the rational images of the packet's electromagnetic and
visible cards agree with the P627 axis-derived quantities. -/
theorem qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_axisValues :
    (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.alphaDenominator : ℚ) =
        alphaStrongQCDPoincareStructuralAlphaEMDenominator ∧
      (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.visibleGauge : ℚ) =
        alphaStrongQCDPoincareVisibleGaugeFromAxis ∧
      (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.unifiedGaugeFreedom : ℚ) =
        su7GaugeFreedomDimension ℚ ∧
      (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.unit : ℚ) = 1 := by
  constructor
  · rw [alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_137]
    norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket]
  constructor
  · rw [alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine]
    norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket]
  constructor
  · norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket,
      su7GaugeFreedomDimension]
  · norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket]

/-- THEOREM 5: the P627-axis CKM packet satisfies the P617 four-card source
equations. -/
theorem qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_sourceEquations :
    CKMSectorAxisPrimitiveCardSourceEquations
      qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket := by
  constructor
  · norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket,
      alphaEMIntegerDenominator]
  constructor
  · norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket,
      visibleGaugeCarrierCardFromLowEnergyZ_eq_nine]
  constructor
  · norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket,
      su7GaugeFreedomDimension]
  · norm_num [qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket,
      yukawaCoefficientUnitCardZ]

/-- THEOREM 6: the P627-axis CKM packet is the canonical P617 sector-axis
packet. -/
theorem qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_eq_canonical :
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket =
      canonicalCKMSectorAxisPrimitiveCardPacket :=
  eq_canonicalCKMSectorAxisPrimitiveCardPacket_of_sourceEquations
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_sourceEquations

/-- THEOREM 7: the P627-axis CKM packet forces Jarlskog depth sum `386`. -/
theorem qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386 :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ) :=
  ckmSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_sourceEquations

/-! ## Bundled receipt and root connection -/

/-- Compact receipt: the P627 unified QCD/Poincare axis supplies the CKM
sector-axis packet and therefore the Jarlskog depth sum `386`. -/
structure QCDPoincareUnifiedAxisCKMProducerReceipt where
  sector_gap :
    qcdPoincareUnifiedAxisCKMSectorGap = (193 : ℚ)
  twice_sector_gap :
    2 * qcdPoincareUnifiedAxisCKMSectorGap = (386 : ℚ)
  packet_axis_values :
    (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.alphaDenominator : ℚ) =
        alphaStrongQCDPoincareStructuralAlphaEMDenominator ∧
      (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.visibleGauge : ℚ) =
        alphaStrongQCDPoincareVisibleGaugeFromAxis ∧
      (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.unifiedGaugeFreedom : ℚ) =
        su7GaugeFreedomDimension ℚ ∧
      (qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket.unit : ℚ) = 1
  source_equations :
    CKMSectorAxisPrimitiveCardSourceEquations
      qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket
  canonical_packet :
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket =
      canonicalCKMSectorAxisPrimitiveCardPacket
  jarlskog_depth_sum :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ)

/-- THEOREM 8: bundled P627-axis CKM producer receipt. -/
theorem qcdPoincareUnifiedAxisCKMProducerReceipt :
    QCDPoincareUnifiedAxisCKMProducerReceipt where
  sector_gap := qcdPoincareUnifiedAxisCKMSectorGap_eq_193
  twice_sector_gap := twice_qcdPoincareUnifiedAxisCKMSectorGap_eq_386
  packet_axis_values :=
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_axisValues
  source_equations :=
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_sourceEquations
  canonical_packet :=
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_eq_canonical
  jarlskog_depth_sum :=
    qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386

end StandardModelConstraint

/-- Current unified finite root with both alpha_s and CKM/Jarlskog routed
through the P627 QCD/Poincare unified axis. -/
structure CurrentUnifiedEquationUnifiedAxisCKMCoreCertificate where
  unified_axis_finite_core :
    CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate
  ckm_unified_axis :
    StandardModelConstraint.QCDPoincareUnifiedAxisCKMProducerReceipt
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        StandardModelConstraint.alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  ckm_depth_sum_from_axis :
    StandardModelConstraint.ckmJarlskogDepthSumFromRationalGrid
        (StandardModelConstraint.gridOfStencil
          (StandardModelConstraint.rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            StandardModelConstraint.qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ)

/-- THEOREM 9: current unified finite root with the CKM sector-axis nail also
connected to the P627 QCD/Poincare axis. -/
def currentUnifiedEquationUnifiedAxisCKMCoreCertificate :
    CurrentUnifiedEquationUnifiedAxisCKMCoreCertificate where
  unified_axis_finite_core :=
    currentUnifiedEquationUnifiedAxisFiniteCoreCertificate
  ckm_unified_axis :=
    StandardModelConstraint.qcdPoincareUnifiedAxisCKMProducerReceipt
  alpha_s_residual :=
    CurrentUnifiedEquationUnifiedAxisFiniteCoreCertificate.alpha_s_residual_eq
      currentUnifiedEquationUnifiedAxisFiniteCoreCertificate
  ckm_depth_sum_from_axis :=
    StandardModelConstraint.qcdPoincareUnifiedAxisCKMSectorAxisPrimitiveCardPacket_jarlskogDepthSum_eq_386

end SaturationMonoid
