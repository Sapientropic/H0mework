import Mathlib.Tactic
import H0mework.Physics.AlphaSources.P461
import H0mework.Physics.AlphaSources.P520

/-!
# Proposition 521: alpha_s residual conservation and non-one-loop necessity

P461 proves the current QCD carrier receipt: the `3+2+1+1` SU(7) block
incidence plus the standard one-loop beta-coefficient formula forces
`b0 = 7`.

P520 lowers the remaining strong-coupling discrepancy to the producer
coordinate:

`alpha_s(displayed) - alpha_s(two-loop-SM output) = 89 / 10000`.

This file welds the two facts into a sharper target.  The one-loop QCD carrier
is already fixed, and the displayed alpha-level residual is strictly positive.
Consequently, any successful four-source residual producer must genuinely
produce that residual: the all-zero source assignment is impossible, and if the
four physical source contributions are assumed nonnegative, at least one source
must be positive.

Boundary: this is still not the threshold / three-loop / representation
calculation.  It is the conservation law that the physical calculation must
satisfy.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The one-loop carrier leaves a strict alpha-level residual -/

/-- THEOREM 1: the SU(7) QCD carrier is fixed at `b0 = 7`, and the alpha_s
residual left after the current two-loop output is exactly `89/10000`. -/
theorem qcdCarrierB0FinalReceipt_beta7_and_alphaStrongGap :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7 ∧
      alphaStrongTwoLoopSMDisplayedGap ℚ = (89 : ℚ) / 10000 :=
  ⟨RunningSigmaBeta.qcdCarrierB0FinalReceipt.beta_formula,
    alphaStrongTwoLoopAlphaGap_eq_89_div_10000⟩

/-- THEOREM 2: the current two-loop output is not already the displayed
strong-coupling anchor. -/
theorem alphaStrongTwoLoopSMOutput_ne_displayed :
    alphaStrongTwoLoopSMOutput ℚ ≠ alphaStrongDisplayed ℚ := by
  norm_num [alphaStrongTwoLoopSMOutput, alphaStrongDisplayed]

/-- THEOREM 3: equivalently, the alpha-level gap left by the current two-loop
output is nonzero. -/
theorem alphaStrongTwoLoopSMDisplayedGap_ne_zero :
    alphaStrongTwoLoopSMDisplayedGap ℚ ≠ 0 := by
  norm_num [alphaStrongTwoLoopSMDisplayedGap, alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-- THEOREM 4: the alpha-level residual is strictly positive.  In alpha
coordinates the displayed anchor lies above the current two-loop output; in
inverse coordinates the same correction is negative, as P289/P520 record. -/
theorem alphaStrongTwoLoopSMDisplayedGap_pos :
    0 < alphaStrongTwoLoopSMDisplayedGap ℚ := by
  norm_num [alphaStrongTwoLoopSMDisplayedGap, alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-! ## Four-source residual conservation -/

namespace AlphaStrongResidualGapProducer

/-- THEOREM 5: a four-source alpha_s residual producer has total produced gap
`89/10000`. -/
theorem producedGap_eq_89_div_10000
    (P : AlphaStrongResidualGapProducer) :
    P.producedGap = (89 : ℚ) / 10000 := by
  rw [producedGap, P.total_gap, alphaStrongTwoLoopAlphaGap_eq_89_div_10000]

/-- THEOREM 6: a four-source alpha_s residual producer has strictly positive
total produced alpha-gap. -/
theorem producedGap_pos
    (P : AlphaStrongResidualGapProducer) :
    0 < P.producedGap := by
  rw [P.producedGap_eq_89_div_10000]
  norm_num

/-- THEOREM 7: although the alpha-level produced gap is positive, its
inverse-coupling-coordinate image is exactly the negative P289 residual
correction. -/
theorem producedGap_inverseCorrection_negative
    (P : AlphaStrongResidualGapProducer) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        P.producedGap < 0 := by
  rw [P.inverseCorrection_eq_target]
  exact alphaStrongResidualInverseCorrectionNeeded_lt_zero ℚ

/-- THEOREM 8: no successful four-source producer can assign zero contribution
to every physical source. -/
theorem not_all_sources_zero
    (P : AlphaStrongResidualGapProducer) :
    ¬ ∀ s : AlphaStrongResidualSource, P.contribution s = 0 := by
  intro hzero
  have hgap := P.total_gap
  rw [hzero AlphaStrongResidualSource.su7Breaking,
    hzero AlphaStrongResidualSource.threshold,
    hzero AlphaStrongResidualSource.threeLoopRG,
    hzero AlphaStrongResidualSource.higgsExtraRepresentation,
    alphaStrongTwoLoopAlphaGap_eq_89_div_10000] at hgap
  norm_num at hgap

/-- THEOREM 9: every successful four-source producer has at least one nonzero
physical source contribution. -/
theorem exists_nonzero_source
    (P : AlphaStrongResidualGapProducer) :
    ∃ s : AlphaStrongResidualSource, P.contribution s ≠ 0 := by
  by_contra hnone
  have hzero : ∀ s : AlphaStrongResidualSource, P.contribution s = 0 := by
    intro s
    by_contra hs
    exact hnone ⟨s, hs⟩
  exact P.not_all_sources_zero hzero

/-- THEOREM 10: every successful four-source producer has at least one
strictly positive alpha-level source contribution.  No nonnegativity side
condition is needed: the four contributions have strictly positive total. -/
theorem exists_positive_source
    (P : AlphaStrongResidualGapProducer) :
    ∃ s : AlphaStrongResidualSource, 0 < P.contribution s := by
  by_contra hnone
  have hnonpos : ∀ s : AlphaStrongResidualSource, P.contribution s ≤ 0 := by
    intro s
    have hs : ¬ 0 < P.contribution s := by
      intro hpos
      exact hnone ⟨s, hpos⟩
    exact le_of_not_gt hs
  have hsum_nonpos : P.producedGap ≤ 0 := by
    unfold producedGap
    linarith [hnonpos AlphaStrongResidualSource.su7Breaking,
      hnonpos AlphaStrongResidualSource.threshold,
      hnonpos AlphaStrongResidualSource.threeLoopRG,
      hnonpos AlphaStrongResidualSource.higgsExtraRepresentation]
  have hsum_pos : 0 < P.producedGap := P.producedGap_pos
  linarith

/-- THEOREM 11: if SU(7)-breaking and threshold sources are declared zero, the
remaining three-loop and Higgs/extra-representation sources must carry the
whole alpha-level residual. -/
theorem threeLoop_plus_higgsExtra_eq_gap_of_su7_threshold_zero
    (P : AlphaStrongResidualGapProducer)
    (hsu7 : P.contribution .su7Breaking = 0)
    (hthreshold : P.contribution .threshold = 0) :
    P.contribution .threeLoopRG +
        P.contribution .higgsExtraRepresentation =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  have h := P.total_gap
  rw [hsu7, hthreshold] at h
  linarith

end AlphaStrongResidualGapProducer

/-! ## Bundled receipt -/

/-- A compact receipt: the one-loop QCD carrier is fixed, but it leaves a
strict positive residual that any successful residual producer must carry. -/
structure AlphaStrongResidualNecessityReceipt where
  qcd_beta :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7
  alpha_gap :
    alphaStrongTwoLoopSMDisplayedGap ℚ = (89 : ℚ) / 10000
  alpha_gap_positive :
    0 < alphaStrongTwoLoopSMDisplayedGap ℚ
  producer_needs_nonzero_source :
    ∀ P : AlphaStrongResidualGapProducer,
      ∃ s : AlphaStrongResidualSource, P.contribution s ≠ 0
  producer_needs_positive_source :
    ∀ P : AlphaStrongResidualGapProducer,
      ∃ s : AlphaStrongResidualSource, 0 < P.contribution s

/-- THEOREM 12: the alpha_s residual necessity receipt. -/
theorem alphaStrongResidualNecessityReceipt :
    AlphaStrongResidualNecessityReceipt where
  qcd_beta := RunningSigmaBeta.qcdCarrierB0FinalReceipt.beta_formula
  alpha_gap := alphaStrongTwoLoopAlphaGap_eq_89_div_10000
  alpha_gap_positive := alphaStrongTwoLoopSMDisplayedGap_pos
  producer_needs_nonzero_source := fun P => P.exists_nonzero_source
  producer_needs_positive_source := fun P => P.exists_positive_source

end StandardModelConstraint
end SaturationMonoid
