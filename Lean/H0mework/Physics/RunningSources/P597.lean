import Mathlib.Tactic
import H0mework.Physics.JointSources.P523
import H0mework.Physics.AlphaSources.P581

/-!
# Proposition 597: closed-loop SU(7) alpha_s residual producer

P581 gives a finite SU(7)-breaking alpha-gap producer:

`(137 - 48) / (9 + 1)^4 = 89 / 10000`.

P523 packages the finite SU(7) representation-physicalization layer:
concrete block embedding, anomaly cancellation, oriented hypercharge
uniqueness, block-incidence matter carrier, and QCD `b0 = 7`.

This file fuses them into one `alpha_s` closed-loop receipt.  It also makes the
P581 source assignment explicit as a singleton contribution law: SU(7)-breaking
carries the finite alpha gap and the three remaining residual sources are zero.

Boundary: this is still the finite SU(7)-breaking producer, not a full
threshold / three-loop / Higgs-spectrum computation.  The gain is that the
current `-89000/128511` inverse residual target is now emitted from one
representation-plus-finite-breaking certificate rather than from separated
bookkeeping receipts.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The finite SU(7)-breaking contribution law -/

/-- The finite source law used by the current closed-loop `alpha_s` producer:
SU(7)-breaking contributes the P581 finite gap, and threshold, three-loop RG,
and Higgs/extra-representation contributions are zero. -/
def AlphaStrongSU7FiniteContributionLaw
    (c : AlphaStrongResidualSource -> ℚ) : Prop :=
  c .su7Breaking = alphaStrongSU7BreakingAlphaGap ℚ ∧
    c .threshold = 0 ∧
      c .threeLoopRG = 0 ∧
        c .higgsExtraRepresentation = 0

/-- THEOREM 1: P581's concrete producer satisfies the finite SU(7)-breaking
contribution law. -/
theorem alphaStrongSU7BreakingResidualGapProducer_contributionLaw :
    AlphaStrongSU7FiniteContributionLaw
      alphaStrongSU7BreakingResidualGapProducer.contribution := by
  simp [AlphaStrongSU7FiniteContributionLaw,
    alphaStrongSU7BreakingResidualGapProducer]

/-- THEOREM 2: the finite SU(7)-breaking contribution law is a singleton law
on contribution functions. -/
theorem alphaStrongSU7FiniteContributionLaw_unique
    (c d : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c)
    (hd : AlphaStrongSU7FiniteContributionLaw d) :
    c = d := by
  funext s
  rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
  rcases hd with ⟨hd_su7, hd_threshold, hd_three, hd_higgs⟩
  cases s <;> simp [hc_su7, hc_threshold, hc_three, hc_higgs,
    hd_su7, hd_threshold, hd_three, hd_higgs]

/-- THEOREM 3: any contribution function satisfying the finite SU(7)-breaking
law produces the alpha-level residual gap `89/10000`. -/
theorem alphaStrongSU7FiniteContributionLaw_total_gap
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    c .su7Breaking + c .threshold + c .threeLoopRG +
        c .higgsExtraRepresentation =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
  rw [hc_su7, hc_threshold, hc_three, hc_higgs,
    alphaStrongSU7BreakingAlphaGap_eq_89_div_10000,
    alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  norm_num

/-- A producer generated from any contribution function satisfying the finite
SU(7)-breaking law. -/
def alphaStrongGapProducerOfSU7FiniteContributionLaw
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    AlphaStrongResidualGapProducer where
  contribution := c
  total_gap := alphaStrongSU7FiniteContributionLaw_total_gap c hc

/-- THEOREM 4: every producer generated from the finite SU(7)-breaking law
has produced gap `89/10000`. -/
theorem alphaStrongGapProducerOfSU7FiniteContributionLaw_gap
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    (alphaStrongGapProducerOfSU7FiniteContributionLaw c hc).producedGap =
      (89 : ℚ) / 10000 :=
  (alphaStrongGapProducerOfSU7FiniteContributionLaw c hc).producedGap_eq_89_div_10000

/-- THEOREM 5: every producer generated from the finite SU(7)-breaking law
transports to the exact P289/P520 inverse residual target. -/
theorem alphaStrongGapProducerOfSU7FiniteContributionLaw_inverseCorrection
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongGapProducerOfSU7FiniteContributionLaw c hc).producedGap =
      alphaStrongResidualInverseCorrectionNeeded ℚ :=
  (alphaStrongGapProducerOfSU7FiniteContributionLaw c hc).inverseCorrection_eq_target

/-- THEOREM 6: every producer generated from the finite SU(7)-breaking law
gives the closed-form inverse residual `-89000/128511`. -/
theorem alphaStrongGapProducerOfSU7FiniteContributionLaw_inverseCorrection_eq_neg
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongGapProducerOfSU7FiniteContributionLaw c hc).producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongGapProducerOfSU7FiniteContributionLaw_inverseCorrection c hc]
  exact alphaStrongResidualInverseCorrectionNeeded_eq ℚ

/-- THEOREM 7: every producer generated from the finite SU(7)-breaking law
closes the direct displayed strong-coupling value. -/
theorem alphaStrongGapProducerOfSU7FiniteContributionLaw_closes_displayedAlpha
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongGapProducerOfSU7FiniteContributionLaw c hc).producedGap) =
      alphaStrongDisplayed ℚ :=
  (alphaStrongGapProducerOfSU7FiniteContributionLaw c hc).closes_displayedAlpha

/-! ## Closed-loop receipt -/

/-- Closed-loop finite SU(7) `alpha_s` residual producer receipt.

The receipt keeps both sides in one object:

* representation physicalization supplies the concrete block embedding,
  anomaly/hypercharge consistency, matter carrier, and QCD `b0 = 7`;
* finite SU(7)-breaking supplies the unique contribution law whose
  inverse-coordinate image is the exact residual target `-89000/128511`;
* the corrected direct alpha value is exactly `1179/10000`.
-/
structure AlphaStrongClosedLoopSU7ProducerReceipt where
  representation :
    SU7RepresentationPhysicalizationReceipt
  finite_breaking :
    AlphaStrongSU7BreakingProducerReceipt
  contribution_law :
    AlphaStrongSU7FiniteContributionLaw
      alphaStrongSU7BreakingResidualGapProducer.contribution
  contribution_law_unique :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ->
        c = alphaStrongSU7BreakingResidualGapProducer.contribution
  qcd_b0 :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7
  alpha_gap :
    alphaStrongSU7BreakingResidualGapProducer.producedGap =
      (89 : ℚ) / 10000
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongSU7BreakingResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 8: the closed-loop finite SU(7) `alpha_s` residual producer
receipt is inhabited. -/
noncomputable def alphaStrongClosedLoopSU7ProducerReceipt :
    AlphaStrongClosedLoopSU7ProducerReceipt where
  representation := su7RepresentationPhysicalizationReceipt
  finite_breaking := alphaStrongSU7BreakingProducerReceipt
  contribution_law := alphaStrongSU7BreakingResidualGapProducer_contributionLaw
  contribution_law_unique := by
    intro c hc
    exact alphaStrongSU7FiniteContributionLaw_unique
      c alphaStrongSU7BreakingResidualGapProducer.contribution
      hc alphaStrongSU7BreakingResidualGapProducer_contributionLaw
  qcd_b0 := RunningSigmaBeta.qcdCarrierB0FinalReceipt.beta_formula
  alpha_gap := alphaStrongSU7BreakingResidualGapProducer_gap
  inverse_residual := by
    rw [alphaStrongSU7BreakingResidualGapProducer_inverseCorrection]
    exact alphaStrongResidualInverseCorrectionNeeded_eq ℚ
  closes_displayed_alpha :=
    alphaStrongSU7BreakingResidualGapProducer_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
