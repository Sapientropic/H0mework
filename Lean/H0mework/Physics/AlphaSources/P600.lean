import Mathlib.Tactic
import H0mework.Physics.AlphaSources.P598

/-!
# Proposition 600: finite-carrier producer for the alpha_s residual gap

P598 made the finite SU(7)-breaking alpha gap a singleton equation surface.
This file lowers that equation surface one layer: the numerator and denominator
are not bare numerals, but cardinalities of finite carriers.

* The numerator carrier is the finite contrast between the electromagnetic
  structural carrier
  `seven-facet Boolean states ⊕ low-energy visible gauge directions`
  and the unified `SU(7)` gauge-freedom carrier.
* The denominator carrier is the four-dimensional resolution carrier
  `(low-energy visible gauge directions ⊕ unit)^4`.

The resulting cardinality-produced candidate satisfies the P598 carrier
equations, so it inherits the exact `89/10000` alpha gap, the inverse residual
`-89000/128511`, and displayed `alpha_s` closure.

Boundary: this is still a finite carrier producer, not a threshold / three-loop
/ Higgs-spectrum dynamics theorem.  The gain is that the P598 equations are now
fed by typed finite carriers rather than by untyped decimal numerals.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Finite carriers for the numerator -/

/-- The seven-facet Boolean carrier: one Boolean choice for each of the seven
primitive semantic axes. -/
abbrev SevenFacetBooleanCarrier :=
  Fin 7 -> Bool

/-- THEOREM 1: the seven-facet Boolean carrier has cardinality `2^7 = 128`. -/
theorem sevenFacetBooleanCarrier_card_eq_128 :
    Fintype.card SevenFacetBooleanCarrier = 128 := by
  simp [SevenFacetBooleanCarrier]

/-- The structural electromagnetic-denominator carrier:
seven-facet information states plus low-energy visible gauge directions. -/
abbrev AlphaEMStructuralCarrier :=
  SevenFacetBooleanCarrier ⊕ LowEnergyVisibleGaugeCarrier

/-- THEOREM 2: the structural electromagnetic carrier has cardinality `137`. -/
theorem alphaEMStructuralCarrier_card_eq_137 :
    Fintype.card AlphaEMStructuralCarrier = 137 := by
  change Fintype.card ((Fin 7 -> Bool) ⊕ (Fin 8 ⊕ Fin 1)) = 137
  simp

/-- The finite contrast carrier between the structural electromagnetic carrier
and the unified `SU(7)` gauge-freedom carrier.  Its definition is the finite
cardinality difference; the theorem below evaluates it to `89`. -/
abbrev AlphaEMGaugeContrastCarrier :=
  Fin (Fintype.card AlphaEMStructuralCarrier -
    Fintype.card UnifiedGaugeFreedomCarrier)

/-- THEOREM 3: the finite numerator contrast carrier has cardinality `89`. -/
theorem alphaEMGaugeContrastCarrier_card_eq_89 :
    Fintype.card AlphaEMGaugeContrastCarrier = 89 := by
  change Fintype.card
      (Fin (Fintype.card AlphaEMStructuralCarrier -
        Fintype.card UnifiedGaugeFreedomCarrier)) = 89
  rw [Fintype.card_fin, alphaEMStructuralCarrier_card_eq_137,
    unifiedGaugeFreedomCarrier_card_eq_48]

/-! ## Finite carriers for the denominator -/

/-- One finite resolution axis: visible low-energy gauge directions plus a
unit/basepoint direction. -/
abbrev AlphaStrongResolutionAxis :=
  LowEnergyVisibleGaugeCarrier ⊕ Fin 1

/-- THEOREM 4: one finite resolution axis has cardinality `10`. -/
theorem alphaStrongResolutionAxis_card_eq_ten :
    Fintype.card AlphaStrongResolutionAxis = 10 := by
  rw [show Fintype.card AlphaStrongResolutionAxis =
      Fintype.card LowEnergyVisibleGaugeCarrier + Fintype.card (Fin 1) by rfl]
  rw [lowEnergyVisibleGaugeCarrier_card_eq_nine]
  norm_num

/-- The four-dimensional resolution carrier used by the finite `alpha_s`
producer. -/
abbrev AlphaStrongFourDimensionalResolutionCarrier :=
  Fin alphaStrongResidualResolutionExponent -> AlphaStrongResolutionAxis

/-- THEOREM 5: the four-dimensional resolution carrier has cardinality
`10^4 = 10000`. -/
theorem alphaStrongFourDimensionalResolutionCarrier_card_eq_10000 :
    Fintype.card AlphaStrongFourDimensionalResolutionCarrier = 10000 := by
  rw [show Fintype.card AlphaStrongFourDimensionalResolutionCarrier =
      Fintype.card AlphaStrongResolutionAxis ^
        Fintype.card (Fin alphaStrongResidualResolutionExponent) by
        exact Fintype.card_fun]
  rw [alphaStrongResolutionAxis_card_eq_ten]
  norm_num [alphaStrongResidualResolutionExponent]

/-! ## Feeding the P598 carrier-equation surface -/

/-- Numerator read from the finite contrast carrier. -/
def alphaStrongFiniteCarrierNumerator : ℚ :=
  (Fintype.card AlphaEMGaugeContrastCarrier : ℚ)

/-- Denominator read from the four-dimensional finite resolution carrier. -/
def alphaStrongFiniteCarrierDenominator : ℚ :=
  (Fintype.card AlphaStrongFourDimensionalResolutionCarrier : ℚ)

/-- Candidate alpha-gap coordinates produced by finite carriers. -/
def finiteCarrierAlphaStrongSU7BreakingGapCandidate :
    AlphaStrongSU7BreakingGapCandidate where
  numerator := alphaStrongFiniteCarrierNumerator
  denominator := alphaStrongFiniteCarrierDenominator
  gap := alphaStrongFiniteCarrierNumerator /
    alphaStrongFiniteCarrierDenominator

/-- THEOREM 6: the finite carrier numerator is the P598 numerator expression. -/
theorem alphaStrongFiniteCarrierNumerator_eq_p598_numerator :
    alphaStrongFiniteCarrierNumerator =
      alphaEMIntegerDenominator ℚ - su7GaugeFreedomDimension ℚ := by
  rw [alphaStrongFiniteCarrierNumerator]
  rw [alphaEMGaugeContrastCarrier_card_eq_89]
  norm_num [alphaEMIntegerDenominator, su7GaugeFreedomDimension]

/-- THEOREM 7: the finite carrier denominator is the P598 denominator
expression. -/
theorem alphaStrongFiniteCarrierDenominator_eq_p598_denominator :
    alphaStrongFiniteCarrierDenominator =
      (lowEnergyVisibleGaugeDimensionFromCard ℚ + 1) ^
        alphaStrongResidualResolutionExponent := by
  rw [alphaStrongFiniteCarrierDenominator]
  rw [alphaStrongFourDimensionalResolutionCarrier_card_eq_10000]
  rw [lowEnergyVisibleGaugeDimensionFromCard_eq_nine]
  norm_num [alphaStrongResidualResolutionExponent]

/-- THEOREM 8: the finite-carrier-produced candidate satisfies the P598
carrier equations. -/
theorem finiteCarrierAlphaStrongSU7BreakingGapCandidate_equations :
    AlphaStrongSU7BreakingGapCarrierEquations
      finiteCarrierAlphaStrongSU7BreakingGapCandidate := by
  constructor
  · exact alphaStrongFiniteCarrierNumerator_eq_p598_numerator
  constructor
  · exact alphaStrongFiniteCarrierDenominator_eq_p598_denominator
  · rfl

/-- THEOREM 9: the finite-carrier-produced candidate is the unique P598
carrier-sourced alpha-gap candidate. -/
theorem finiteCarrierAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate =
      carrierSourcedAlphaStrongSU7BreakingGapCandidate :=
  eq_carrierSourcedAlphaStrongGapCandidate_of_equations
    finiteCarrierAlphaStrongSU7BreakingGapCandidate
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_equations

/-- THEOREM 10: the finite carriers produce the exact alpha gap `89/10000`. -/
theorem finiteCarrierAlphaStrongSU7BreakingGapCandidate_gap :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      (89 : ℚ) / 10000 :=
  alphaStrongGapCandidate_gap_eq_89_div_10000
    finiteCarrierAlphaStrongSU7BreakingGapCandidate
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_equations

/-- THEOREM 11: the finite-carrier gap maps directly to the exact inverse
residual, without routing through the displayed-gap target theorem. -/
theorem finiteCarrierAlphaStrongSU7BreakingGapCandidate_inverseCorrection_direct :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      -((89000 : ℚ) / 128511) := by
  rw [finiteCarrierAlphaStrongSU7BreakingGapCandidate_gap]
  norm_num [inverseCorrectionFromAlphaGap, alphaStrongTwoLoopSMOutput]

/-- THEOREM 12: the finite-carrier gap transports to the exact inverse
residual `-89000/128511`. -/
theorem finiteCarrierAlphaStrongSU7BreakingGapCandidate_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongGapCandidate_inverseCorrection_eq_neg
    finiteCarrierAlphaStrongSU7BreakingGapCandidate
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_equations

/-- THEOREM 13: the finite-carrier gap closes the displayed strong coupling. -/
theorem finiteCarrierAlphaStrongSU7BreakingGapCandidate_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap) =
      alphaStrongDisplayed ℚ :=
  alphaStrongGapCandidate_closes_displayedAlpha
    finiteCarrierAlphaStrongSU7BreakingGapCandidate
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_equations

/-! ## Bundled receipt -/

/-- Receipt for the finite-cardinality producer feeding P598. -/
structure AlphaStrongFiniteCarrierGapProducerReceipt where
  seven_facet_card :
    Fintype.card SevenFacetBooleanCarrier = 128
  alpha_em_structural_card :
    Fintype.card AlphaEMStructuralCarrier = 137
  numerator_card :
    Fintype.card AlphaEMGaugeContrastCarrier = 89
  resolution_axis_card :
    Fintype.card AlphaStrongResolutionAxis = 10
  denominator_card :
    Fintype.card AlphaStrongFourDimensionalResolutionCarrier = 10000
  equations :
    AlphaStrongSU7BreakingGapCarrierEquations
      finiteCarrierAlphaStrongSU7BreakingGapCandidate
  unique_candidate :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate =
      carrierSourcedAlphaStrongSU7BreakingGapCandidate
  gap :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      (89 : ℚ) / 10000
  direct_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      -((89000 : ℚ) / 128511)
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 14: bundled finite-carrier producer receipt. -/
theorem alphaStrongFiniteCarrierGapProducerReceipt :
    AlphaStrongFiniteCarrierGapProducerReceipt where
  seven_facet_card := sevenFacetBooleanCarrier_card_eq_128
  alpha_em_structural_card := alphaEMStructuralCarrier_card_eq_137
  numerator_card := alphaEMGaugeContrastCarrier_card_eq_89
  resolution_axis_card := alphaStrongResolutionAxis_card_eq_ten
  denominator_card :=
    alphaStrongFourDimensionalResolutionCarrier_card_eq_10000
  equations := finiteCarrierAlphaStrongSU7BreakingGapCandidate_equations
  unique_candidate :=
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced
  gap := finiteCarrierAlphaStrongSU7BreakingGapCandidate_gap
  direct_inverse_residual :=
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_inverseCorrection_direct
  inverse_residual :=
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_inverseCorrection
  closes_displayed_alpha :=
    finiteCarrierAlphaStrongSU7BreakingGapCandidate_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
