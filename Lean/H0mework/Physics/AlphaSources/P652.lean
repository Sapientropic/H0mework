import Mathlib.Tactic
import H0mework.Physics.AlphaSources.P600
import H0mework.Realization.Relations.P651

/-!
# Proposition 652: alpha_s residual closed finite-cardinality formula

P651 packages the current three-nail root: the formal physical `alpha_s`
producer is object-equal to the canonical finite SU(7)-breaking residual
producer, and that producer transports to the inverse residual
`-89000/128511`.

This file tightens the alpha nail by exposing the producer's closed finite
cardinality formula:

`((2^7 + (8 + 1)) - (7^2 - 1)) / (8 + 1 + 1)^4`.

In words: seven-facet information states plus low-energy visible gauge
directions, minus unified SU(7) gauge freedom, divided by the four-dimensional
visible-gauge-plus-unit resolution carrier.  The formula is definitionally the
P600 finite carrier gap, and therefore the same gap carried by the canonical
SU(7)-breaking source in P651.

Boundary: this is still the finite-cardinality producer, not a smooth
threshold-spectrum / three-loop-RG / Higgs-extra-representation dynamics
calculation.  It removes the remaining presentation ambiguity around the
finite producer's number.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Closed finite-cardinality gap -/

/-- The alpha-level residual gap read directly from the P600 finite carriers. -/
def alphaStrongFiniteCardinalityClosedGap : ℚ :=
  alphaStrongFiniteCarrierNumerator / alphaStrongFiniteCarrierDenominator

/-- THEOREM 1: the closed gap is exactly the gap coordinate of the finite
carrier candidate. -/
theorem finiteCarrierAlphaStrongSU7BreakingGapCandidate_gap_eq_closedFormula :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      alphaStrongFiniteCardinalityClosedGap := by
  rfl

/-- THEOREM 2: in visible finite-cardinality coordinates, the alpha residual
gap is

`((2^7 + (8 + 1)) - (7^2 - 1)) / (8 + 1 + 1)^4`.

This is the carrier-level formula for the `89/10000` gap. -/
theorem alphaStrongFiniteCardinalityClosedGap_eq_su7_block_formula :
    alphaStrongFiniteCardinalityClosedGap =
      ((((2 : ℚ) ^ 7 + ((8 : ℚ) + 1)) - ((7 : ℚ) ^ 2 - 1)) /
        (((8 : ℚ) + 1 + 1) ^ 4)) := by
  rw [alphaStrongFiniteCardinalityClosedGap,
    alphaStrongFiniteCarrierNumerator,
    alphaStrongFiniteCarrierDenominator]
  rw [alphaEMGaugeContrastCarrier_card_eq_89,
    alphaStrongFourDimensionalResolutionCarrier_card_eq_10000]
  norm_num

/-- THEOREM 3: the closed finite-cardinality formula evaluates to
`89/10000`. -/
theorem alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000 :
    alphaStrongFiniteCardinalityClosedGap = (89 : ℚ) / 10000 := by
  rw [alphaStrongFiniteCardinalityClosedGap_eq_su7_block_formula]
  norm_num

/-- THEOREM 4: the closed finite-cardinality formula is the produced gap of the
canonical SU(7)-breaking residual producer. -/
theorem alphaStrongSU7BreakingResidualGapProducer_producedGap_eq_closedFormula :
    alphaStrongSU7BreakingResidualGapProducer.producedGap =
      alphaStrongFiniteCardinalityClosedGap := by
  rw [alphaStrongSU7BreakingResidualGapProducer_gap,
    alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000]

/-- THEOREM 5: the canonical SU(7)-breaking source contribution itself is the
closed finite-cardinality formula. -/
theorem alphaStrongSU7BreakingResidualGapProducer_su7Contribution_eq_closedFormula :
    alphaStrongSU7BreakingResidualGapProducer.contribution .su7Breaking =
      alphaStrongFiniteCardinalityClosedGap := by
  have hlaw := alphaStrongSU7BreakingResidualGapProducer_contributionLaw
  rcases hlaw with ⟨hsu7, _, _, _⟩
  rw [hsu7, alphaStrongSU7BreakingAlphaGap_eq_89_div_10000,
    alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000]

/-- THEOREM 6: transported through inverse-coupling coordinates, the closed
finite-cardinality gap is exactly the required inverse residual. -/
theorem alphaStrongFiniteCardinalityClosedGap_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongFiniteCardinalityClosedGap =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000,
    ← alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  exact inverseGapImage_eq_neg_89000_div_128511

/-- THEOREM 7: the closed finite-cardinality gap closes the displayed direct
strong coupling. -/
theorem alphaStrongFiniteCardinalityClosedGap_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongFiniteCardinalityClosedGap) =
      alphaStrongDisplayed ℚ := by
  rw [alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000,
    ← alphaStrongTwoLoopAlphaGap_eq_89_div_10000,
    ← alphaStrongResidualInverseCorrection_eq_inverseGapImage]
  exact alphaStrongResidualInverseCorrection_closes_displayedAlpha

/-! ## Certificate -/

/-- Compact certificate: the current `alpha_s` residual producer is not just
an assigned rational.  Its alpha-level gap is the closed finite-cardinality
formula, and that formula is the canonical SU(7)-breaking source gap exposed by
the current P651 root. -/
structure AlphaStrongFiniteCardinalityClosedFormulaProducerCertificate where
  finite_carrier :
    AlphaStrongFiniteCarrierGapProducerReceipt
  root :
    CurrentUnifiedEquationPrimeShadowThreeNailRootCertificate
  visible_block_formula :
    alphaStrongFiniteCardinalityClosedGap =
      ((((2 : ℚ) ^ 7 + ((8 : ℚ) + 1)) - ((7 : ℚ) ^ 2 - 1)) /
        (((8 : ℚ) + 1 + 1) ^ 4))
  gap :
    alphaStrongFiniteCardinalityClosedGap = (89 : ℚ) / 10000
  canonical_producer_gap :
    alphaStrongSU7BreakingResidualGapProducer.producedGap =
      alphaStrongFiniteCardinalityClosedGap
  canonical_su7_source_gap :
    alphaStrongSU7BreakingResidualGapProducer.contribution .su7Breaking =
      alphaStrongFiniteCardinalityClosedGap
  physical_alpha_object_eq_canonical_su7 :
    alphaStrongPhysicalFiniteGeometryProducer
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongSU7BreakingResidualGapProducer
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongFiniteCardinalityClosedGap =
      -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongFiniteCardinalityClosedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 8: closed finite-cardinality alpha residual producer certificate. -/
noncomputable def alphaStrongFiniteCardinalityClosedFormulaProducerCertificate :
    AlphaStrongFiniteCardinalityClosedFormulaProducerCertificate where
  finite_carrier := alphaStrongFiniteCarrierGapProducerReceipt
  root := currentUnifiedEquationPrimeShadowThreeNailRootCertificate
  visible_block_formula :=
    alphaStrongFiniteCardinalityClosedGap_eq_su7_block_formula
  gap := alphaStrongFiniteCardinalityClosedGap_eq_89_div_10000
  canonical_producer_gap :=
    alphaStrongSU7BreakingResidualGapProducer_producedGap_eq_closedFormula
  canonical_su7_source_gap :=
    alphaStrongSU7BreakingResidualGapProducer_su7Contribution_eq_closedFormula
  physical_alpha_object_eq_canonical_su7 :=
    currentUnifiedEquationPrimeShadowThreeNailRootCertificate
      |>.physical_alpha_object_eq_canonical_su7
  inverse_residual :=
    alphaStrongFiniteCardinalityClosedGap_inverseCorrection
  closes_displayed_alpha :=
    alphaStrongFiniteCardinalityClosedGap_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
