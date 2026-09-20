import Mathlib.Tactic
import H0mework.Physics.JointSources.P371
import H0mework.Physics.RunningSources.P521

/-!
# Proposition 581: a concrete SU(7)-breaking producer for the alpha_s residual

P520/P521 reduce the `alpha_s` producer debt to one alpha-coordinate number:

`alpha_s(displayed) - alpha_s(two-loop output) = 89 / 10000`.

This file supplies the first concrete producer candidate for that number from
already proved finite gauge data, rather than from the displayed `alpha_s`
anchor:

* the numerator is the gauge/information breaking contrast
  `alphaEMIntegerDenominator - dim(SU(7)) = 137 - 48 = 89`;
* the scale denominator is `(visible low-energy gauge carrier + unit)^4 =
  (9 + 1)^4 = 10000`.

The resulting SU(7)-breaking contribution is therefore

`(137 - 48) / (9 + 1)^4 = 89 / 10000`,

with the other three P520 residual sources set to zero.  P520 then transports
this alpha-level producer through the inverse-coupling coordinate and closes
the displayed strong coupling.

Boundary: this is the finite SU(7)-breaking producer candidate.  It does not
replace a full threshold / three-loop / Higgs-spectrum calculation; it makes
the proposed producer formula exact and machine-checkable.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The finite SU(7)-breaking residual formula -/

/-- The four-dimensional resolution exponent used by the finite producer.
It is kept as a named constant so the producer formula exposes its geometric
scale assumption instead of hiding `10000` as a decimal display artifact. -/
def alphaStrongResidualResolutionExponent : Nat := 4

/-- The producer denominator:
`(low-energy visible gauge carrier + unit)^4 = (9 + 1)^4 = 10000`. -/
def alphaStrongSU7BreakingScaleDenominator
    (K : Type*) [Field K] : K :=
  (lowEnergyVisibleGaugeDimensionFromCard K + (1 : K)) ^
    alphaStrongResidualResolutionExponent

/-- THEOREM 1: the finite producer denominator is exactly `10000`. -/
theorem alphaStrongSU7BreakingScaleDenominator_eq_10000
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongSU7BreakingScaleDenominator K = (10000 : K) := by
  rw [alphaStrongSU7BreakingScaleDenominator,
    lowEnergyVisibleGaugeDimensionFromCard_eq_nine]
  norm_num [alphaStrongResidualResolutionExponent]

/-- The numerator of the finite producer:
low-energy electromagnetic integer denominator minus unified SU(7) freedom. -/
def alphaStrongSU7BreakingNumerator
    (K : Type*) [Ring K] : K :=
  alphaEMIntegerDenominator K - su7GaugeFreedomDimension K

/-- THEOREM 2: the finite SU(7)-breaking numerator is `137 - 48 = 89`. -/
theorem alphaStrongSU7BreakingNumerator_eq_89
    (K : Type*) [Ring K] :
    alphaStrongSU7BreakingNumerator K = (89 : K) := by
  norm_num [alphaStrongSU7BreakingNumerator, alphaEMIntegerDenominator,
    sevenFacetInformationStateCount, su7GaugeFreedomDimension]

/-- The SU(7)-breaking alpha-level residual contribution. -/
def alphaStrongSU7BreakingAlphaGap
    (K : Type*) [Field K] : K :=
  alphaStrongSU7BreakingNumerator K /
    alphaStrongSU7BreakingScaleDenominator K

/-- THEOREM 3: the SU(7)-breaking producer gives the P520 alpha gap
`89/10000`, without reading the displayed `alpha_s` anchor in its definition.
-/
theorem alphaStrongSU7BreakingAlphaGap_eq_89_div_10000
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongSU7BreakingAlphaGap K = (89 : K) / (10000 : K) := by
  rw [alphaStrongSU7BreakingAlphaGap,
    alphaStrongSU7BreakingNumerator_eq_89,
    alphaStrongSU7BreakingScaleDenominator_eq_10000]

/-! ## Feeding the P520 four-source producer -/

/-- The concrete four-source residual producer whose entire alpha-level gap is
carried by the SU(7)-breaking source. -/
def alphaStrongSU7BreakingResidualGapProducer :
    AlphaStrongResidualGapProducer where
  contribution
    | .su7Breaking => alphaStrongSU7BreakingAlphaGap ℚ
    | .threshold => 0
    | .threeLoopRG => 0
    | .higgsExtraRepresentation => 0
  total_gap := by
    change
      alphaStrongSU7BreakingAlphaGap ℚ + 0 + 0 + 0 =
        alphaStrongTwoLoopSMDisplayedGap ℚ
    rw [alphaStrongSU7BreakingAlphaGap_eq_89_div_10000,
      alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
    norm_num

/-- THEOREM 4: the concrete SU(7)-breaking producer has produced gap
`89/10000`. -/
theorem alphaStrongSU7BreakingResidualGapProducer_gap :
    alphaStrongSU7BreakingResidualGapProducer.producedGap =
      (89 : ℚ) / 10000 :=
  alphaStrongSU7BreakingResidualGapProducer.producedGap_eq_89_div_10000

/-- THEOREM 5: the concrete producer transports to the P289 inverse-coordinate
target `-89000/128511`. -/
theorem alphaStrongSU7BreakingResidualGapProducer_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingResidualGapProducer.producedGap =
      alphaStrongResidualInverseCorrectionNeeded ℚ :=
  alphaStrongSU7BreakingResidualGapProducer.inverseCorrection_eq_target

/-- THEOREM 6: the same concrete producer closes the direct displayed
strong-coupling alpha value after inverse-coordinate transport. -/
theorem alphaStrongSU7BreakingResidualGapProducer_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongSU7BreakingResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ :=
  alphaStrongSU7BreakingResidualGapProducer.closes_displayedAlpha

/-! ## Bundled receipt -/

/-- A compact receipt for the concrete finite SU(7)-breaking residual
producer. -/
structure AlphaStrongSU7BreakingProducerReceipt where
  numerator :
    alphaStrongSU7BreakingNumerator ℚ = (89 : ℚ)
  denominator :
    alphaStrongSU7BreakingScaleDenominator ℚ = (10000 : ℚ)
  alpha_gap :
    alphaStrongSU7BreakingAlphaGap ℚ = (89 : ℚ) / 10000
  inverse_target :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingResidualGapProducer.producedGap =
      alphaStrongResidualInverseCorrectionNeeded ℚ
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongSU7BreakingResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 7: the finite SU(7)-breaking producer receipt. -/
theorem alphaStrongSU7BreakingProducerReceipt :
    AlphaStrongSU7BreakingProducerReceipt where
  numerator := alphaStrongSU7BreakingNumerator_eq_89 ℚ
  denominator := alphaStrongSU7BreakingScaleDenominator_eq_10000 ℚ
  alpha_gap := alphaStrongSU7BreakingAlphaGap_eq_89_div_10000 ℚ
  inverse_target :=
    alphaStrongSU7BreakingResidualGapProducer_inverseCorrection
  closes_displayed_alpha :=
    alphaStrongSU7BreakingResidualGapProducer_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
