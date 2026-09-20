import H0mework.Physics.RunningSources.P858

/-!
# Proposition 864: direct alpha_s residual from the fully generated vector

P858 generated the four alpha-strong source coordinates from finite spectra:

* SU(7)-breaking trace imbalance;
* threshold trace balance;
* generated two/three-loop RG spectrum;
* Higgs/extra representation trace balance;
* generated QCD/Poincare resolution denominator.

This file removes the last return through the old packet/primitive equality
for the numerical readout.  The fully generated vector is summed directly over
the exhaustive four-source carrier, giving `89/10000`, and the inverse
coordinate is then computed directly as `-89000/128511`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open scoped BigOperators

set_option linter.defProp false

/-! ## Direct sum of the fully generated four-source vector -/

/-- THEOREM 1: the fully generated four-source vector has total alpha-level
gap `89/10000`, by direct finite-source summation. -/
theorem alphaStrongFullyGeneratedFourSourceVector_sum_eq_89_div_10000 :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFullyGeneratedFourSourceVector s) =
        (89 : ℚ) / 10000 := by
  rw [alphaStrongResidualSource_univ_sum]
  rw [alphaStrongFullyGeneratedFourSourceVector_su7Breaking,
    alphaStrongFullyGeneratedFourSourceVector_threshold,
    alphaStrongFullyGeneratedFourSourceVector_threeLoopRG,
    alphaStrongFullyGeneratedFourSourceVector_higgsExtra]
  norm_num

/-- THEOREM 2: the same direct sum is exactly the displayed two-loop alpha
gap. -/
theorem alphaStrongFullyGeneratedFourSourceVector_sum_eq_displayedGap :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFullyGeneratedFourSourceVector s) =
        alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rw [alphaStrongFullyGeneratedFourSourceVector_sum_eq_89_div_10000]
  norm_num [alphaStrongTwoLoopSMDisplayedGap, alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-! ## Direct inverse-coordinate readout -/

/-- THEOREM 3: the inverse-coordinate correction of the fully generated
source vector is `-89000/128511`, computed directly from its sum. -/
theorem alphaStrongFullyGeneratedFourSourceVector_inverseCorrection_direct :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFullyGeneratedFourSourceVector s) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongFullyGeneratedFourSourceVector_sum_eq_89_div_10000]
  norm_num [inverseCorrectionFromAlphaGap, alphaStrongTwoLoopSMOutput]

/-- THEOREM 4: the fully generated vector closes the displayed strong coupling
directly after inverse-coordinate transport. -/
theorem alphaStrongFullyGeneratedFourSourceVector_closes_displayed_direct :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource,
              alphaStrongFullyGeneratedFourSourceVector s)) =
      alphaStrongDisplayed ℚ := by
  rw [alphaStrongFullyGeneratedFourSourceVector_inverseCorrection_direct]
  norm_num [alphaStrongTwoLoopSMOutputInverse, alphaStrongDisplayed]

/-- P864 certificate: the generated alpha-strong vector now closes the
residual without detouring through the old packet or primitive equality. -/
structure AlphaStrongFullyGeneratedDirectResidualCertificate : Prop where
  generated_sum :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFullyGeneratedFourSourceVector s) =
        (89 : ℚ) / 10000
  generated_sum_is_displayed_gap :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFullyGeneratedFourSourceVector s) =
        alphaStrongTwoLoopSMDisplayedGap ℚ
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFullyGeneratedFourSourceVector s) =
      -((89000 : ℚ) / 128511)
  closes_displayed :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource,
              alphaStrongFullyGeneratedFourSourceVector s)) =
      alphaStrongDisplayed ℚ

def alphaStrongFullyGeneratedDirectResidualCertificate :
    AlphaStrongFullyGeneratedDirectResidualCertificate where
  generated_sum := alphaStrongFullyGeneratedFourSourceVector_sum_eq_89_div_10000
  generated_sum_is_displayed_gap :=
    alphaStrongFullyGeneratedFourSourceVector_sum_eq_displayedGap
  inverse_residual :=
    alphaStrongFullyGeneratedFourSourceVector_inverseCorrection_direct
  closes_displayed :=
    alphaStrongFullyGeneratedFourSourceVector_closes_displayed_direct


end
end StandardModelConstraint
end SaturationMonoid
