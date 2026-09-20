import H0mework.Realization.Relations.P528

/-!
# Proposition 529: exact normal form for the alpha_s four-source producer

P527 made the alpha_s residual source surface finite and exhaustive, and
showed that any closed four-source receipt transports to the exact inverse
correction and displayed alpha_s anchor.

This file removes one last interface ambiguity: the four-source closure receipt
is not an extra wrapper over `AlphaStrongResidualGapProducer`.  It is exactly
the finite normal form of that producer.

So the remaining physical calculation can target either object:

* a contribution function on the four-source enum with total gap;
* four explicitly named source contributions with total gap.

Lean proves these are equivalent.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

namespace AlphaStrongResidualGapProducer

/-- Two residual-gap producers are equal when their finite source contribution
functions are equal.  The `total_gap` field is proof data, so proof
irrelevance removes it once the computational field is fixed. -/
theorem ext
    {P Q : AlphaStrongResidualGapProducer}
    (h : ∀ s : AlphaStrongResidualSource, P.contribution s = Q.contribution s) :
    P = Q := by
  cases P with
  | mk pc pt =>
    cases Q with
    | mk qc qt =>
      have hfun : pc = qc := funext h
      subst qc
      congr

/-- THEOREM 1: every abstract residual-gap producer has an explicit four-source
closure receipt. -/
def toFourSourceClosureReceipt
    (P : AlphaStrongResidualGapProducer) :
    AlphaStrongFourSourceClosureReceipt where
  su7_breaking := P.contribution .su7Breaking
  threshold := P.contribution .threshold
  three_loop_rg := P.contribution .threeLoopRG
  higgs_extra_representation := P.contribution .higgsExtraRepresentation
  total_gap := by
    simpa [producedGap] using P.total_gap

end AlphaStrongResidualGapProducer

namespace AlphaStrongFourSourceClosureReceipt

/-- THEOREM 2: converting an explicit closure receipt to an abstract producer
and back is identity. -/
theorem toGapProducer_toFourSourceClosureReceipt
    (R : AlphaStrongFourSourceClosureReceipt) :
    R.toGapProducer.toFourSourceClosureReceipt = R := by
  cases R
  simp [toGapProducer, AlphaStrongResidualGapProducer.toFourSourceClosureReceipt,
    contribution]

end AlphaStrongFourSourceClosureReceipt

namespace AlphaStrongResidualGapProducer

/-- THEOREM 3: converting an abstract producer to the explicit four-source
receipt and back is identity. -/
theorem toFourSourceClosureReceipt_toGapProducer
    (P : AlphaStrongResidualGapProducer) :
    P.toFourSourceClosureReceipt.toGapProducer = P := by
  apply ext
  intro s
  cases s <;> rfl

end AlphaStrongResidualGapProducer

/-! ## Equivalence and exact gate certificate -/

/-- THEOREM 4: the explicit four-source closure receipt is equivalent to the
original alpha_s residual-gap producer. -/
def alphaStrongFourSourceClosureEquivGapProducer :
    AlphaStrongFourSourceClosureReceipt ≃ AlphaStrongResidualGapProducer where
  toFun := AlphaStrongFourSourceClosureReceipt.toGapProducer
  invFun := AlphaStrongResidualGapProducer.toFourSourceClosureReceipt
  left_inv := AlphaStrongFourSourceClosureReceipt.toGapProducer_toFourSourceClosureReceipt
  right_inv := AlphaStrongResidualGapProducer.toFourSourceClosureReceipt_toGapProducer

/-- Compact certificate that P527's explicit four-source receipt is an exact
normal form for P520's residual-gap producer. -/
structure AlphaStrongFourSourceExactNormalFormCertificate where
  equiv :
    AlphaStrongFourSourceClosureReceipt ≃ AlphaStrongResidualGapProducer
  receipt_to_producer_closes_displayed :
    ∀ R : AlphaStrongFourSourceClosureReceipt,
      (1 : ℚ) /
          (alphaStrongTwoLoopSMOutputInverse ℚ +
            inverseCorrectionFromAlphaGap
              (alphaStrongTwoLoopSMOutput ℚ)
              (∑ s : AlphaStrongResidualSource, R.contribution s)) =
        alphaStrongDisplayed ℚ
  producer_to_receipt_closes_displayed :
    ∀ P : AlphaStrongResidualGapProducer,
      (1 : ℚ) /
          (alphaStrongTwoLoopSMOutputInverse ℚ +
            inverseCorrectionFromAlphaGap
              (alphaStrongTwoLoopSMOutput ℚ)
              (∑ s : AlphaStrongResidualSource,
                P.toFourSourceClosureReceipt.contribution s)) =
        alphaStrongDisplayed ℚ

/-- THEOREM 5: the exact normal form certificate for the alpha_s four-source
producer. -/
def alphaStrongFourSourceExactNormalFormCertificate :
    AlphaStrongFourSourceExactNormalFormCertificate where
  equiv := alphaStrongFourSourceClosureEquivGapProducer
  receipt_to_producer_closes_displayed := by
    intro R
    exact R.closes_displayedAlpha
  producer_to_receipt_closes_displayed := by
    intro P
    exact P.toFourSourceClosureReceipt.closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
