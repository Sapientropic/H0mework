import Mathlib.Tactic
import H0mework.Physics.YukawaSources.P654

/-!
# Proposition 655: alpha_s closed gap from the QCD/Poincare producer axis

P652 exposed the current `alpha_s` residual as the closed finite-cardinality
formula

`((2^7 + (8 + 1)) - (7^2 - 1)) / (8 + 1 + 1)^4 = 89/10000`.

This file welds that presentation back to the upstream finite producer from
P626/P632:

`axis = b0_QCD + PoincareSlots_4D = 7 + 3 = 10`.

Thus the denominator in the closed `alpha_s` gap is not an independent
visible-cardinality choice.  It is the fourth power of the already checked
QCD/Poincare producer axis, and the same gap transports to the exact inverse
residual `-89000/128511`.

Boundary: this still is not the missing smooth SU(7)-threshold / three-loop-RG
/ Higgs-spectrum dynamics calculation.  It is the finite producer bridge that
keeps the `alpha_s` nail tied to the existing representation/RG and Poincare
carriers.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The QCD/Poincare closed alpha gap -/

/-- The closed `alpha_s` gap read from the QCD/Poincare producer axis:

`finite numerator / (b0_QCD + PoincareSlots_4D)^4`. -/
def alphaStrongQCDPoincareClosedGap : ℚ :=
  (Fintype.card AlphaEMGaugeContrastCarrier : ℚ) /
    (alphaStrongQCDPoincareResolutionAxis ^
      alphaStrongResidualResolutionExponent)

/-- The displayed block formula with `a = b0_QCD + PoincareSlots_4D`. -/
def alphaStrongQCDPoincareAxisBlockFormula : ℚ :=
  let a : ℚ :=
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput +
      (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ)
  ((((2 : ℚ) ^ 7 + (a - 1)) - ((7 : ℚ) ^ 2 - 1)) /
    (a ^ alphaStrongResidualResolutionExponent))

/-- THEOREM 1: the QCD/Poincare closed gap is the literal finite block formula
with axis `b0_QCD + PoincareSlots_4D`. -/
theorem alphaStrongQCDPoincareClosedGap_eq_qcd_poincare_block_formula :
    alphaStrongQCDPoincareClosedGap =
      alphaStrongQCDPoincareAxisBlockFormula := by
  rw [alphaStrongQCDPoincareClosedGap,
    alphaStrongQCDPoincareAxisBlockFormula,
    alphaStrongQCDPoincareResolutionAxis]
  rw [RunningSigmaBeta.qcd_b0_from_final_carrier_formula,
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three,
    alphaEMGaugeContrastCarrier_card_eq_89]
  norm_num [alphaStrongResidualResolutionExponent]

/-- THEOREM 2: the QCD/Poincare closed gap agrees with P652's finite-cardinality
closed gap. -/
theorem alphaStrongQCDPoincareClosedGap_eq_finiteCardinalityClosedGap :
    alphaStrongQCDPoincareClosedGap =
      alphaStrongFiniteCardinalityClosedGap := by
  rw [alphaStrongQCDPoincareClosedGap_eq_qcd_poincare_block_formula,
    alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000]
  norm_num [alphaStrongQCDPoincareAxisBlockFormula,
    RunningSigmaBeta.qcd_b0_from_final_carrier_formula,
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three,
    alphaStrongResidualResolutionExponent]

/-- THEOREM 3: the QCD/Poincare producer axis gives the alpha-level gap
`89/10000`. -/
theorem alphaStrongQCDPoincareClosedGap_eq_89_div_10000 :
    alphaStrongQCDPoincareClosedGap = (89 : ℚ) / 10000 := by
  rw [alphaStrongQCDPoincareClosedGap_eq_finiteCardinalityClosedGap,
    alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000]

/-- THEOREM 4: in inverse-coupling coordinates, the QCD/Poincare closed gap is
exactly the needed residual `-89000/128511`. -/
theorem alphaStrongQCDPoincareClosedGap_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongQCDPoincareClosedGap_eq_finiteCardinalityClosedGap]
  exact alphaStrongFiniteCardinalityClosedGap_inverseCorrection

/-- THEOREM 5: the QCD/Poincare closed gap closes the displayed direct
strong-coupling value. -/
theorem alphaStrongQCDPoincareClosedGap_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareClosedGap) =
      alphaStrongDisplayed ℚ := by
  rw [alphaStrongQCDPoincareClosedGap_eq_finiteCardinalityClosedGap]
  exact alphaStrongFiniteCardinalityClosedGap_closes_displayedAlpha

/-- THEOREM 6: the named QCD/Poincare residual producer carries the same
closed gap on its active SU(7)-breaking source. -/
theorem alphaStrongQCDPoincareResidualGapProducer_producedGap_eq_closedGap
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (alphaStrongQCDPoincareResidualGapProducer e).producedGap =
      alphaStrongQCDPoincareClosedGap := by
  rw [alphaStrongQCDPoincareClosedGap_eq_89_div_10000]
  exact
    alphaStrongGapProducerOfSU7FiniteContributionLaw_gap
      (alphaStrongQCDPoincareContribution e)
      (alphaStrongQCDPoincareContribution_law e)

/-! ## Certificate -/

/-- Compact certificate: the current finite `alpha_s` residual has a closed
formula whose denominator is produced by the QCD one-loop carrier plus the 4D
Poincare slot carrier. -/
structure AlphaStrongQCDPoincareClosedGapProducerCertificate where
  qcd_poincare :
    AlphaStrongQCDPoincareProducerReceipt unifiedGaugeIntoAlphaEMStructural
  finite_cardinality :
    AlphaStrongFiniteCardinalityClosedFormulaProducerCertificate
  qcd_b0 :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7
  poincare_slots :
    AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 = 3
  axis :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ)
  qcd_poincare_block_formula :
    alphaStrongQCDPoincareClosedGap =
      alphaStrongQCDPoincareAxisBlockFormula
  matches_finite_cardinality :
    alphaStrongQCDPoincareClosedGap =
      alphaStrongFiniteCardinalityClosedGap
  gap :
    alphaStrongQCDPoincareClosedGap = (89 : ℚ) / 10000
  producer_gap :
    (alphaStrongQCDPoincareResidualGapProducer
      unifiedGaugeIntoAlphaEMStructural).producedGap =
        alphaStrongQCDPoincareClosedGap
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareClosedGap =
      -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongQCDPoincareClosedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 7: closed QCD/Poincare alpha residual producer certificate. -/
def alphaStrongQCDPoincareClosedGapProducerCertificate :
    AlphaStrongQCDPoincareClosedGapProducerCertificate where
  qcd_poincare :=
    alphaStrongQCDPoincareProducerReceipt unifiedGaugeIntoAlphaEMStructural
  finite_cardinality :=
    alphaStrongFiniteCardinalityClosedFormulaProducerCertificate
  qcd_b0 := RunningSigmaBeta.qcd_b0_from_final_carrier_formula
  poincare_slots :=
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three
  axis := alphaStrongQCDPoincareResolutionAxis_eq_ten
  qcd_poincare_block_formula :=
    alphaStrongQCDPoincareClosedGap_eq_qcd_poincare_block_formula
  matches_finite_cardinality :=
    alphaStrongQCDPoincareClosedGap_eq_finiteCardinalityClosedGap
  gap := alphaStrongQCDPoincareClosedGap_eq_89_div_10000
  producer_gap :=
    alphaStrongQCDPoincareResidualGapProducer_producedGap_eq_closedGap
      unifiedGaugeIntoAlphaEMStructural
  inverse_residual := alphaStrongQCDPoincareClosedGap_inverseCorrection
  closes_displayed_alpha :=
    alphaStrongQCDPoincareClosedGap_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
