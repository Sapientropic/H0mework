import Mathlib.Tactic
import H0mework.Physics.RunningSources.P597

/-!
# Proposition 598: singleton carrier-equation surface for the alpha_s gap

P581 introduced the finite SU(7)-breaking alpha-gap formula

`(137 - 48) / (9 + 1)^4 = 89 / 10000`.

P597 fused that formula with the SU(7) representation-physicalization receipt
and the four-source contribution law.  This file lowers the target one step:
the alpha-gap formula itself is expressed as a finite carrier-equation surface.

A candidate has three coordinates: numerator, denominator, and alpha gap.  The
carrier equations force:

* numerator = `alphaEMIntegerDenominator - dim(SU(7))`;
* denominator = `(low-energy visible gauge carrier + unit)^4`;
* gap = numerator / denominator.

The accepted candidate surface is a singleton, and its unique gap transports
through P520 to the inverse residual `-89000/128511` and direct displayed
`alpha_s = 1179/10000`.

Boundary: this still does not derive the carrier equations from a full
threshold / three-loop / Higgs-spectrum calculation.  It makes the finite
equation target itself no-free and machine-checkable.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Candidate surface -/

/-- Candidate coordinates for the finite SU(7)-breaking alpha-gap producer. -/
@[ext]
structure AlphaStrongSU7BreakingGapCandidate where
  numerator : ℚ
  denominator : ℚ
  gap : ℚ

/-- The canonical carrier-sourced candidate from P581. -/
def carrierSourcedAlphaStrongSU7BreakingGapCandidate :
    AlphaStrongSU7BreakingGapCandidate where
  numerator := alphaStrongSU7BreakingNumerator ℚ
  denominator := alphaStrongSU7BreakingScaleDenominator ℚ
  gap := alphaStrongSU7BreakingAlphaGap ℚ

/-- Carrier equations selecting the finite SU(7)-breaking alpha-gap candidate.

This is the narrow target a deeper threshold / breaking-spectrum producer must
hit if it wants to feed the existing closed-loop alpha_s receipt. -/
def AlphaStrongSU7BreakingGapCarrierEquations
    (C : AlphaStrongSU7BreakingGapCandidate) : Prop :=
  C.numerator = alphaEMIntegerDenominator ℚ - su7GaugeFreedomDimension ℚ ∧
    C.denominator =
      (lowEnergyVisibleGaugeDimensionFromCard ℚ + 1) ^
        alphaStrongResidualResolutionExponent ∧
    C.gap = C.numerator / C.denominator

/-! ## The carrier-equation surface is a singleton -/

/-- THEOREM 1: the canonical candidate satisfies the carrier equations. -/
theorem carrierSourcedAlphaStrongSU7BreakingGapCandidate_equations :
    AlphaStrongSU7BreakingGapCarrierEquations
      carrierSourcedAlphaStrongSU7BreakingGapCandidate := by
  simp [AlphaStrongSU7BreakingGapCarrierEquations,
    carrierSourcedAlphaStrongSU7BreakingGapCandidate,
    alphaStrongSU7BreakingNumerator,
    alphaStrongSU7BreakingScaleDenominator,
    alphaStrongSU7BreakingAlphaGap]

/-- THEOREM 2: the carrier equations force the canonical candidate. -/
theorem eq_carrierSourcedAlphaStrongGapCandidate_of_equations
    (C : AlphaStrongSU7BreakingGapCandidate)
    (hC : AlphaStrongSU7BreakingGapCarrierEquations C) :
    C = carrierSourcedAlphaStrongSU7BreakingGapCandidate := by
  rcases hC with ⟨hnum, hden, hgap⟩
  ext <;>
    simp [carrierSourcedAlphaStrongSU7BreakingGapCandidate,
      alphaStrongSU7BreakingNumerator,
      alphaStrongSU7BreakingScaleDenominator,
      alphaStrongSU7BreakingAlphaGap,
      hnum, hden, hgap]

/-- A finite candidate surface has no free alpha-gap parameter when any two
accepted candidates are equal. -/
def NoContinuousFreeAlphaStrongGapCandidateParameters
    (constraints : AlphaStrongSU7BreakingGapCandidate -> Prop) : Prop :=
  ∀ C D : AlphaStrongSU7BreakingGapCandidate,
    constraints C -> constraints D -> C = D

/-- THEOREM 3: the finite SU(7)-breaking alpha-gap carrier-equation surface is
a singleton/no-free surface. -/
theorem alphaStrongSU7BreakingGapCarrierEquations_noContinuousFree :
    NoContinuousFreeAlphaStrongGapCandidateParameters
      AlphaStrongSU7BreakingGapCarrierEquations := by
  intro C D hC hD
  rw [eq_carrierSourcedAlphaStrongGapCandidate_of_equations C hC,
    eq_carrierSourcedAlphaStrongGapCandidate_of_equations D hD]

/-! ## Numeric and alpha_s consequences -/

/-- THEOREM 4: any carrier-equation candidate has numerator `89`. -/
theorem alphaStrongGapCandidate_numerator_eq_89
    (C : AlphaStrongSU7BreakingGapCandidate)
    (hC : AlphaStrongSU7BreakingGapCarrierEquations C) :
    C.numerator = (89 : ℚ) := by
  rw [eq_carrierSourcedAlphaStrongGapCandidate_of_equations C hC]
  exact alphaStrongSU7BreakingNumerator_eq_89 ℚ

/-- THEOREM 5: any carrier-equation candidate has denominator `10000`. -/
theorem alphaStrongGapCandidate_denominator_eq_10000
    (C : AlphaStrongSU7BreakingGapCandidate)
    (hC : AlphaStrongSU7BreakingGapCarrierEquations C) :
    C.denominator = (10000 : ℚ) := by
  rw [eq_carrierSourcedAlphaStrongGapCandidate_of_equations C hC]
  exact alphaStrongSU7BreakingScaleDenominator_eq_10000 ℚ

/-- THEOREM 6: any carrier-equation candidate has alpha gap `89/10000`. -/
theorem alphaStrongGapCandidate_gap_eq_89_div_10000
    (C : AlphaStrongSU7BreakingGapCandidate)
    (hC : AlphaStrongSU7BreakingGapCarrierEquations C) :
    C.gap = (89 : ℚ) / 10000 := by
  rw [eq_carrierSourcedAlphaStrongGapCandidate_of_equations C hC]
  exact alphaStrongSU7BreakingAlphaGap_eq_89_div_10000 ℚ

/-- THEOREM 7: any carrier-equation candidate transports to the exact inverse
residual `-89000/128511`. -/
theorem alphaStrongGapCandidate_inverseCorrection_eq_neg
    (C : AlphaStrongSU7BreakingGapCandidate)
    (hC : AlphaStrongSU7BreakingGapCarrierEquations C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ) C.gap =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongGapCandidate_gap_eq_89_div_10000 C hC]
  rw [← alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  exact inverseGapImage_eq_neg_89000_div_128511

/-- THEOREM 8: any carrier-equation candidate closes the direct displayed
strong-coupling alpha value. -/
theorem alphaStrongGapCandidate_closes_displayedAlpha
    (C : AlphaStrongSU7BreakingGapCandidate)
    (hC : AlphaStrongSU7BreakingGapCarrierEquations C) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ) C.gap) =
      alphaStrongDisplayed ℚ := by
  rw [alphaStrongGapCandidate_gap_eq_89_div_10000 C hC]
  rw [← alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  rw [← alphaStrongResidualInverseCorrection_eq_inverseGapImage]
  exact alphaStrongResidualInverseCorrection_closes_displayedAlpha

/-! ## Bundled receipt -/

/-- Compact receipt: the finite SU(7)-breaking alpha-gap carrier equations
select a unique candidate, and that candidate closes the current alpha_s
residual. -/
structure AlphaStrongGapCarrierEquationSingletonReceipt where
  canonical_satisfies :
    AlphaStrongSU7BreakingGapCarrierEquations
      carrierSourcedAlphaStrongSU7BreakingGapCandidate
  unique_candidate :
    ∀ C : AlphaStrongSU7BreakingGapCandidate,
      AlphaStrongSU7BreakingGapCarrierEquations C ->
        C = carrierSourcedAlphaStrongSU7BreakingGapCandidate
  no_free :
    NoContinuousFreeAlphaStrongGapCandidateParameters
      AlphaStrongSU7BreakingGapCarrierEquations
  gap :
    ∀ C : AlphaStrongSU7BreakingGapCandidate,
      AlphaStrongSU7BreakingGapCarrierEquations C ->
        C.gap = (89 : ℚ) / 10000
  inverse_residual :
    ∀ C : AlphaStrongSU7BreakingGapCandidate,
      AlphaStrongSU7BreakingGapCarrierEquations C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ) C.gap =
          -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    ∀ C : AlphaStrongSU7BreakingGapCandidate,
      AlphaStrongSU7BreakingGapCarrierEquations C ->
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ) C.gap) =
          alphaStrongDisplayed ℚ

/-- THEOREM 9: singleton receipt for the finite alpha-gap carrier equations. -/
theorem alphaStrongGapCarrierEquationSingletonReceipt :
    AlphaStrongGapCarrierEquationSingletonReceipt where
  canonical_satisfies :=
    carrierSourcedAlphaStrongSU7BreakingGapCandidate_equations
  unique_candidate :=
    eq_carrierSourcedAlphaStrongGapCandidate_of_equations
  no_free :=
    alphaStrongSU7BreakingGapCarrierEquations_noContinuousFree
  gap :=
    alphaStrongGapCandidate_gap_eq_89_div_10000
  inverse_residual :=
    alphaStrongGapCandidate_inverseCorrection_eq_neg
  closes_displayed_alpha :=
    alphaStrongGapCandidate_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
