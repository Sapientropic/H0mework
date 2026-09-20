import H0mework.Physics.AlphaSources.P626

/-!
# Proposition 627: unified-axis alpha_s producer

P626 lowers the finite `alpha_s` denominator to a single finite axis

`axis = b0_QCD + PoincareSlots_4D = 7 + 3 = 10`.

This file tightens the same producer one notch: the numerator is also rewritten
through that axis, so the finite gap is no longer presented as two independent
integer anchors:

* low-energy visible gauge directions = `axis - 1`;
* electromagnetic denominator = `2^7 + (axis - 1)`;
* SU(7)-breaking numerator =
  `2^7 + (axis - 1) - dim(SU(7)) = 89`;
* denominator = `axis^4 = 10000`.

Therefore the same QCD/Poincare axis produces the whole finite
`89/10000` alpha-gap and still transports to the exact inverse residual
`-89000/128511`.

Boundary: this is still a finite carrier producer.  It does not replace the
remaining smooth physics debt: threshold spectra, three-loop RG, and the
Higgs/extra-representation calculation.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The shared QCD/Poincare axis also reconstructs the numerator -/

/-- Low-energy visible gauge directions recovered from the same QCD/Poincare
axis used in P626: `axis - unit = 10 - 1 = 9`. -/
def alphaStrongQCDPoincareVisibleGaugeFromAxis : ℚ :=
  alphaStrongQCDPoincareResolutionAxis - 1

/-- THEOREM 1: the axis-derived low-energy visible gauge count is `9`. -/
theorem alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine :
    alphaStrongQCDPoincareVisibleGaugeFromAxis = (9 : ℚ) := by
  rw [alphaStrongQCDPoincareVisibleGaugeFromAxis,
    alphaStrongQCDPoincareResolutionAxis_eq_ten]
  norm_num

/-- THEOREM 2: the axis-derived visible gauge count agrees with the P371
low-energy visible-gauge carrier. -/
theorem alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_lowEnergyVisible :
    alphaStrongQCDPoincareVisibleGaugeFromAxis =
      lowEnergyVisibleGaugeDimensionFromCard ℚ := by
  rw [alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine,
    lowEnergyVisibleGaugeDimensionFromCard_eq_nine]

/-- Electromagnetic structural denominator reconstructed from information
states plus the axis-derived visible gauge directions. -/
def alphaStrongQCDPoincareStructuralAlphaEMDenominator : ℚ :=
  sevenFacetInformationStateCount ℚ +
    alphaStrongQCDPoincareVisibleGaugeFromAxis

/-- THEOREM 3: the axis-derived electromagnetic denominator is `137`. -/
theorem alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_137 :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator = (137 : ℚ) := by
  rw [alphaStrongQCDPoincareStructuralAlphaEMDenominator,
    sevenFacetInformationStateCount_eq_128,
    alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine]
  norm_num

/-- THEOREM 4: the axis-derived electromagnetic denominator is exactly the
existing `alphaEMIntegerDenominator`. -/
theorem alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_alphaEMIntegerDenominator :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator =
      alphaEMIntegerDenominator ℚ := by
  rw [alphaStrongQCDPoincareStructuralAlphaEMDenominator,
    alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_lowEnergyVisible]
  exact (alphaEMIntegerDenominator_eq_infoStates_plus_lowEnergyVisibleGauge ℚ).symm

/-- Unified-axis SU(7)-breaking numerator:
`2^7 + (axis - 1) - dim(SU(7))`. -/
def alphaStrongQCDPoincareUnifiedAxisNumerator : ℚ :=
  alphaStrongQCDPoincareStructuralAlphaEMDenominator -
    su7GaugeFreedomDimension ℚ

/-- THEOREM 5: the unified-axis numerator is the P598 numerator expression. -/
theorem alphaStrongQCDPoincareUnifiedAxisNumerator_eq_p598_numerator :
    alphaStrongQCDPoincareUnifiedAxisNumerator =
      alphaEMIntegerDenominator ℚ - su7GaugeFreedomDimension ℚ := by
  rw [alphaStrongQCDPoincareUnifiedAxisNumerator,
    alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_alphaEMIntegerDenominator]

/-- THEOREM 6: the unified-axis numerator is exactly `89`. -/
theorem alphaStrongQCDPoincareUnifiedAxisNumerator_eq_89 :
    alphaStrongQCDPoincareUnifiedAxisNumerator = (89 : ℚ) := by
  rw [alphaStrongQCDPoincareUnifiedAxisNumerator_eq_p598_numerator]
  norm_num [alphaEMIntegerDenominator, su7GaugeFreedomDimension]

/-- THEOREM 7: the unified-axis numerator agrees with the P600 finite-carrier
numerator. -/
theorem alphaStrongQCDPoincareUnifiedAxisNumerator_eq_finiteCarrierNumerator :
    alphaStrongQCDPoincareUnifiedAxisNumerator =
      alphaStrongFiniteCarrierNumerator := by
  rw [alphaStrongQCDPoincareUnifiedAxisNumerator_eq_89,
    alphaStrongFiniteCarrierNumerator,
    alphaEMGaugeContrastCarrier_card_eq_89]
  norm_num

/-! ## Unified-axis alpha-gap candidate -/

/-- The alpha-gap candidate whose numerator and denominator are both produced
from the QCD/Poincare finite axis. -/
def qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate :
    AlphaStrongSU7BreakingGapCandidate where
  numerator := alphaStrongQCDPoincareUnifiedAxisNumerator
  denominator := alphaStrongQCDPoincareResolutionDenominator
  gap :=
    alphaStrongQCDPoincareUnifiedAxisNumerator /
      alphaStrongQCDPoincareResolutionDenominator

/-- THEOREM 8: the unified-axis candidate satisfies the P598 carrier
equations. -/
theorem qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_equations :
    AlphaStrongSU7BreakingGapCarrierEquations
      qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate := by
  constructor
  · exact alphaStrongQCDPoincareUnifiedAxisNumerator_eq_p598_numerator
  constructor
  · rw [qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate,
      alphaStrongQCDPoincareResolutionDenominator_eq_finiteCarrierDenominator]
    exact alphaStrongFiniteCarrierDenominator_eq_p598_denominator
  · rfl

/-- THEOREM 9: the unified-axis candidate is the unique carrier-sourced
alpha-gap candidate. -/
theorem qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced :
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate =
      carrierSourcedAlphaStrongSU7BreakingGapCandidate :=
  eq_carrierSourcedAlphaStrongGapCandidate_of_equations
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_equations

/-- THEOREM 10: the unified-axis candidate produces the exact alpha-gap
`89/10000`. -/
theorem qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_gap :
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate.gap =
      (89 : ℚ) / 10000 :=
  alphaStrongGapCandidate_gap_eq_89_div_10000
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_equations

/-- THEOREM 11: the unified-axis candidate transports to the exact inverse
residual `-89000/128511`. -/
theorem qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate.gap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongGapCandidate_inverseCorrection_eq_neg
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_equations

/-! ## Four-source producer using the unified-axis candidate -/

/-- Four-source contribution law whose unique active source is the
unified-axis SU(7)-breaking gap. -/
def alphaStrongQCDPoincareUnifiedAxisContribution :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate.gap
  | .threshold => 0
  | .threeLoopRG => 0
  | .higgsExtraRepresentation => 0

/-- THEOREM 12: the unified-axis contribution satisfies the finite
SU(7)-breaking source law. -/
theorem alphaStrongQCDPoincareUnifiedAxisContribution_law :
    AlphaStrongSU7FiniteContributionLaw
      alphaStrongQCDPoincareUnifiedAxisContribution := by
  constructor
  · rw [alphaStrongQCDPoincareUnifiedAxisContribution,
      qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced]
    rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The focused residual-gap producer fed by the unified QCD/Poincare axis. -/
def alphaStrongQCDPoincareUnifiedAxisResidualGapProducer :
    AlphaStrongResidualGapProducer :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw
    alphaStrongQCDPoincareUnifiedAxisContribution
    alphaStrongQCDPoincareUnifiedAxisContribution_law

/-- THEOREM 13: the unified-axis four-source producer transports to the exact
inverse residual `-89000/128511`. -/
theorem alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw_inverseCorrection_eq_neg
    alphaStrongQCDPoincareUnifiedAxisContribution
    alphaStrongQCDPoincareUnifiedAxisContribution_law

/-- THEOREM 14: the unified-axis producer closes the displayed strong-coupling
alpha value. -/
theorem alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw_closes_displayedAlpha
    alphaStrongQCDPoincareUnifiedAxisContribution
    alphaStrongQCDPoincareUnifiedAxisContribution_law

/-! ## Bundled receipt -/

/-- Compact receipt: the same QCD/Poincare axis produces the visible-gauge
offset, electromagnetic denominator, SU(7)-breaking numerator, finite
denominator, alpha-gap, and inverse residual. -/
structure AlphaStrongQCDPoincareUnifiedAxisProducerReceipt where
  axis :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ)
  visible_gauge_from_axis :
    alphaStrongQCDPoincareVisibleGaugeFromAxis = (9 : ℚ)
  alpha_em_denominator :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator = (137 : ℚ)
  alpha_em_denominator_eq_standard :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator =
      alphaEMIntegerDenominator ℚ
  numerator :
    alphaStrongQCDPoincareUnifiedAxisNumerator = (89 : ℚ)
  denominator :
    alphaStrongQCDPoincareResolutionDenominator = (10000 : ℚ)
  equations :
    AlphaStrongSU7BreakingGapCarrierEquations
      qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate
  alpha_gap :
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate.gap =
      (89 : ℚ) / 10000
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 15: bundled unified-axis alpha_s residual producer receipt. -/
theorem alphaStrongQCDPoincareUnifiedAxisProducerReceipt :
    AlphaStrongQCDPoincareUnifiedAxisProducerReceipt where
  axis := alphaStrongQCDPoincareResolutionAxis_eq_ten
  visible_gauge_from_axis :=
    alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_nine
  alpha_em_denominator :=
    alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_137
  alpha_em_denominator_eq_standard :=
    alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_alphaEMIntegerDenominator
  numerator := alphaStrongQCDPoincareUnifiedAxisNumerator_eq_89
  denominator := alphaStrongQCDPoincareResolutionDenominator_eq_10000
  equations :=
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_equations
  alpha_gap :=
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_gap
  inverse_residual :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection
  closes_displayed_alpha :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_closes_displayedAlpha

end StandardModelConstraint

/-! ## Connection back to the current unified-equation root -/

/-- Current unified-equation root with the `alpha_s` finite numerator and
denominator both lowered to the shared QCD/Poincare axis. -/
structure CurrentUnifiedEquationAlphaStrongUnifiedAxisCoreCertificate where
  qcd_poincare_core :
    CurrentUnifiedEquationAlphaStrongQCDPoincareCoreCertificate
  unified_axis_alpha_s :
    StandardModelConstraint.AlphaStrongQCDPoincareUnifiedAxisProducerReceipt
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        StandardModelConstraint.alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 16: current unified root with the QCD/Poincare unified-axis
producer attached to the `alpha_s` nail. -/
noncomputable def currentUnifiedEquationAlphaStrongUnifiedAxisCoreCertificate :
    CurrentUnifiedEquationAlphaStrongUnifiedAxisCoreCertificate where
  qcd_poincare_core :=
    currentUnifiedEquationAlphaStrongQCDPoincareCoreCertificate
  unified_axis_alpha_s :=
    StandardModelConstraint.alphaStrongQCDPoincareUnifiedAxisProducerReceipt
  alpha_s_residual :=
    StandardModelConstraint.alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection

end SaturationMonoid
