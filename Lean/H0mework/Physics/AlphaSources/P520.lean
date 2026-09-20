import Mathlib.Tactic
import H0mework.Physics.RunningSources.P519

/-!
# Proposition 520: alpha_s residual producer, inverse-coordinate bridge

P289 isolated the remaining strong-coupling residual as the exact inverse
correction

`-89000 / 128511`.

This file lowers that target to the producer coordinate that the physics side
should actually attack.  The ugly inverse-coupling fraction is exactly the
image of the ordinary alpha-level gap

`1179/10000 - 109/1000 = 89/10000`

under the inverse-coupling coordinate map `a ↦ 1/a`.

So a future SU(7)-breaking / threshold / three-loop / extra-representation
producer does not need to guess `-89000/128511` directly.  It can produce the
alpha-level residual gap `89/10000`; Lean then transports it to the inverse
coordinate and proves that the corrected strong coupling closes to the displayed
anchor.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Inverse-coordinate image of an alpha-level gap -/

/-- The inverse-coupling shift induced by moving an alpha value `a` by `gap`. -/
def inverseCorrectionFromAlphaGap (a gap : ℚ) : ℚ :=
  (1 : ℚ) / (a + gap) - (1 : ℚ) / a

/-- THEOREM 1: the displayed alpha-level gap from the two-loop output is
`89/10000`. -/
theorem alphaStrongTwoLoopAlphaGap_eq_89_div_10000 :
    alphaStrongTwoLoopSMDisplayedGap ℚ = (89 : ℚ) / 10000 := by
  norm_num [alphaStrongTwoLoopSMDisplayedGap, alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-- THEOREM 2: the inverse-coordinate image of the alpha-level gap is exactly
P289's residual inverse-coupling correction target. -/
theorem alphaStrongResidualInverseCorrection_eq_inverseGapImage :
    alphaStrongResidualInverseCorrectionNeeded ℚ =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongTwoLoopSMDisplayedGap ℚ) := by
  norm_num [alphaStrongResidualInverseCorrectionNeeded,
    alphaStrongDisplayedInverseCorrectionFromCorrectedGUT,
    alphaStrongDisplayedInverse,
    alphaStrongTwoLoopSMInverseCorrection,
    alphaStrongTwoLoopSMOutputInverse,
    alphaGUTInverseSectorNormalized,
    gaugedFundamentalDimension,
    standardModelSloganSectorCount,
    inverseCorrectionFromAlphaGap,
    alphaStrongTwoLoopSMDisplayedGap,
    alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-- THEOREM 3: in closed form, the inverse-coordinate residual is
`-89000/128511`.  The denominator is `109 * 1179`, i.e. old-alpha times
new-alpha denominators after clearing decimals. -/
theorem inverseGapImage_eq_neg_89000_div_128511 :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongTwoLoopSMDisplayedGap ℚ) =
      -((89000 : ℚ) / 128511) := by
  rw [← alphaStrongResidualInverseCorrection_eq_inverseGapImage]
  exact alphaStrongResidualInverseCorrectionNeeded_eq ℚ

/-- THEOREM 4: adding the residual inverse correction to the two-loop inverse
coupling lands exactly on the displayed inverse coupling. -/
theorem alphaStrongTwoLoopInverse_plus_residual_eq_displayedInverse :
    alphaStrongTwoLoopSMOutputInverse ℚ +
      alphaStrongResidualInverseCorrectionNeeded ℚ =
        alphaStrongDisplayedInverse ℚ := by
  norm_num [alphaStrongTwoLoopSMOutputInverse,
    alphaStrongResidualInverseCorrectionNeeded,
    alphaStrongDisplayedInverseCorrectionFromCorrectedGUT,
    alphaStrongDisplayedInverse,
    alphaStrongTwoLoopSMInverseCorrection,
    alphaGUTInverseSectorNormalized,
    gaugedFundamentalDimension,
    standardModelSloganSectorCount]

/-- THEOREM 5: after applying the residual inverse correction, the predicted
strong coupling is exactly the displayed `1179/10000`. -/
theorem alphaStrongResidualInverseCorrection_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          alphaStrongResidualInverseCorrectionNeeded ℚ) =
      alphaStrongDisplayed ℚ := by
  norm_num [alphaStrongTwoLoopSMOutputInverse,
    alphaStrongResidualInverseCorrectionNeeded,
    alphaStrongDisplayedInverseCorrectionFromCorrectedGUT,
    alphaStrongDisplayedInverse,
    alphaStrongTwoLoopSMInverseCorrection,
    alphaGUTInverseSectorNormalized,
    gaugedFundamentalDimension,
    standardModelSloganSectorCount,
    alphaStrongDisplayed]

/-! ## Producer-facing source decomposition -/

/-- The four physical source families named by the roadmap for the residual
alpha_s gap. -/
inductive AlphaStrongResidualSource where
  | su7Breaking
  | threshold
  | threeLoopRG
  | higgsExtraRepresentation
  deriving DecidableEq, Repr

/-- A focused residual-gap producer.  It produces the alpha-level gap; P520
then transports that gap to the inverse-coupling residual target. -/
structure AlphaStrongResidualGapProducer where
  contribution : AlphaStrongResidualSource -> ℚ
  total_gap :
    contribution .su7Breaking +
      contribution .threshold +
        contribution .threeLoopRG +
          contribution .higgsExtraRepresentation =
      alphaStrongTwoLoopSMDisplayedGap ℚ

namespace AlphaStrongResidualGapProducer

/-- The alpha-level gap produced by a source decomposition. -/
def producedGap (P : AlphaStrongResidualGapProducer) : ℚ :=
  P.contribution .su7Breaking +
    P.contribution .threshold +
      P.contribution .threeLoopRG +
        P.contribution .higgsExtraRepresentation

/-- THEOREM 6: any source decomposition producing the alpha-level residual gap
automatically produces the exact P289 inverse-coupling residual target. -/
theorem inverseCorrection_eq_target
    (P : AlphaStrongResidualGapProducer) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        P.producedGap =
      alphaStrongResidualInverseCorrectionNeeded ℚ := by
  rw [producedGap, P.total_gap,
    alphaStrongResidualInverseCorrection_eq_inverseGapImage]

/-- THEOREM 7: any such source decomposition closes the strong coupling to the
displayed alpha anchor after inverse-coordinate transport. -/
theorem closes_displayedAlpha
    (P : AlphaStrongResidualGapProducer) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            P.producedGap) =
      alphaStrongDisplayed ℚ := by
  rw [P.inverseCorrection_eq_target]
  exact alphaStrongResidualInverseCorrection_closes_displayedAlpha

end AlphaStrongResidualGapProducer

end StandardModelConstraint
end SaturationMonoid
