import H0mework.Physics.AlphaSpectrum.P847
import H0mework.Physics.AlphaSources.P864

/-!
# Proposition 867: alpha_s direct residual from the finite-spectrum evaluator

P847 produced the threshold, RG, and Higgs/extra coordinates from finite
representation spectra.  P864 then read the inverse-coordinate residual from
the fully generated four-source vector.

This file removes the remaining seam between those two layers.  The four-source
vector below uses the P847 finite-spectrum evaluator for the three zero
coordinates and the generated SU(7)-breaking numerator/denominator for the
nonzero coordinate.  Its sum and inverse-coordinate residual are computed
directly, so the `-89000/128511` correction is now read from the same
finite-spectrum evaluator that generates the smooth-physics source coordinates.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open scoped BigOperators

set_option linter.defProp false

/-! ## Finite-spectrum evaluator vector -/

/-- The alpha-strong four-source vector with every coordinate read from the
finite-spectrum evaluator layer:

* SU(7)-breaking numerator/denominator from generated finite carriers;
* threshold from the `7 - 7` finite color spectrum;
* RG from the generated two/three-loop finite-spectrum counterterm;
* Higgs/extra from the `6 - 6` finite representation-slot spectrum. -/
def alphaStrongFiniteSpectrumEvaluatorFourSourceVector :
    AlphaStrongResidualSource → ℚ
  | .su7Breaking =>
      alphaStrongSU7BreakingGeneratedImbalance /
        alphaStrongGeneratedResolutionDenominator
  | .threshold => thresholdFiniteSpectrumContribution
  | .threeLoopRG => finiteSpectrumRGMismatch
  | .higgsExtraRepresentation => higgsExtraFiniteSpectrumMismatch

theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_su7Breaking :
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector .su7Breaking =
      89 / 10000 := by
  unfold alphaStrongFiniteSpectrumEvaluatorFourSourceVector
  rw [alphaStrongSU7BreakingGeneratedImbalance_eq_89,
    alphaStrongGeneratedResolutionDenominator_eq_10000]

theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_threshold :
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector .threshold = 0 := by
  unfold alphaStrongFiniteSpectrumEvaluatorFourSourceVector
  exact thresholdFiniteSpectrumContribution_eq_zero

theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_threeLoopRG :
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector .threeLoopRG = 0 := by
  unfold alphaStrongFiniteSpectrumEvaluatorFourSourceVector
  exact finiteSpectrumRGMismatch_eq_zero

theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_higgsExtra :
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector
        .higgsExtraRepresentation = 0 := by
  unfold alphaStrongFiniteSpectrumEvaluatorFourSourceVector
  exact higgsExtraFiniteSpectrumMismatch_eq_zero

/-- THEOREM 1: the P847 finite-spectrum evaluator vector is pointwise the
P858 fully generated vector.  This is the weld from finite representation
spectra to the direct residual readout. -/
theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_eq_fullyGenerated :
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector =
      alphaStrongFullyGeneratedFourSourceVector := by
  funext source
  cases source
  · rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_su7Breaking,
      alphaStrongFullyGeneratedFourSourceVector_su7Breaking]
  · rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_threshold,
      alphaStrongFullyGeneratedFourSourceVector_threshold]
  · rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_threeLoopRG,
      alphaStrongFullyGeneratedFourSourceVector_threeLoopRG]
  · rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_higgsExtra,
      alphaStrongFullyGeneratedFourSourceVector_higgsExtra]

/-! ## Direct residual readout -/

/-- THEOREM 2: direct finite-source summation of the finite-spectrum evaluator
vector gives the displayed alpha-level gap `89/10000`. -/
theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_sum_eq_89_div_10000 :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
        (89 : ℚ) / 10000 := by
  rw [alphaStrongResidualSource_univ_sum]
  rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_su7Breaking,
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_threshold,
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_threeLoopRG,
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_higgsExtra]
  norm_num

/-- THEOREM 3: the finite-spectrum evaluator sum is exactly the displayed
two-loop alpha gap. -/
theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_sum_eq_displayedGap :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
        alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_sum_eq_89_div_10000]
  norm_num [alphaStrongTwoLoopSMDisplayedGap, alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-- THEOREM 4: inverse-coordinate correction read directly from the P847
finite-spectrum evaluator. -/
theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_inverseCorrection_direct :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_sum_eq_89_div_10000]
  norm_num [inverseCorrectionFromAlphaGap, alphaStrongTwoLoopSMOutput]

/-- THEOREM 5: the finite-spectrum evaluator closes the displayed strong
coupling directly after inverse-coordinate transport. -/
theorem alphaStrongFiniteSpectrumEvaluatorFourSourceVector_closes_displayed_direct :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource,
              alphaStrongFiniteSpectrumEvaluatorFourSourceVector s)) =
      alphaStrongDisplayed ℚ := by
  rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_inverseCorrection_direct]
  norm_num [alphaStrongTwoLoopSMOutputInverse, alphaStrongDisplayed]

/-- THEOREM 6: the finite-spectrum evaluator and the fully generated vector
give the same direct inverse residual. -/
theorem alphaStrongFiniteSpectrumEvaluator_inverseCorrection_eq_fullyGenerated :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFullyGeneratedFourSourceVector s) := by
  rw [alphaStrongFiniteSpectrumEvaluatorFourSourceVector_eq_fullyGenerated]

/-! ## Certificate -/

/-- P867 certificate: the finite-spectrum evaluator itself computes the
alpha-strong source gap and inverse-coordinate residual. -/
structure AlphaStrongFiniteSpectrumEvaluatorDirectResidualCertificate :
    Prop where
  vector_eq_fullyGenerated :
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector =
      alphaStrongFullyGeneratedFourSourceVector
  generated_sum :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
        (89 : ℚ) / 10000
  generated_sum_is_displayed_gap :
    (∑ s : AlphaStrongResidualSource,
      alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
        alphaStrongTwoLoopSMDisplayedGap ℚ
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
      -((89000 : ℚ) / 128511)
  closes_displayed :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource,
              alphaStrongFiniteSpectrumEvaluatorFourSourceVector s)) =
      alphaStrongDisplayed ℚ
  inverse_matches_fullyGenerated :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFiniteSpectrumEvaluatorFourSourceVector s) =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFullyGeneratedFourSourceVector s)

def alphaStrongFiniteSpectrumEvaluatorDirectResidualCertificate :
    AlphaStrongFiniteSpectrumEvaluatorDirectResidualCertificate where
  vector_eq_fullyGenerated :=
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_eq_fullyGenerated
  generated_sum :=
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_sum_eq_89_div_10000
  generated_sum_is_displayed_gap :=
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_sum_eq_displayedGap
  inverse_residual :=
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_inverseCorrection_direct
  closes_displayed :=
    alphaStrongFiniteSpectrumEvaluatorFourSourceVector_closes_displayed_direct
  inverse_matches_fullyGenerated :=
    alphaStrongFiniteSpectrumEvaluator_inverseCorrection_eq_fullyGenerated


end
end StandardModelConstraint
end SaturationMonoid
