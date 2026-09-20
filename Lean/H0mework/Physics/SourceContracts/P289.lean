/-
  Proposition 289: residual inverse-coupling correction target.

  P288 fixed the corrected GUT inverse-coupling anchor

      alpha_GUT^{-1} = (2^7 + 5) / 3 = 133 / 3,

  and recorded the current two-loop-SM displayed strong-coupling output

      alpha_s(M_Z) = 109 / 1000.

  This file isolates the remaining correction target: the exact inverse-
  coupling shift that a future threshold / three-loop / representation producer
  must add on top of the two-loop-SM correction in order to hit the displayed
  observational anchor used by P287.

  Boundary: this is still arithmetic bookkeeping, not a threshold calculation.
  Its purpose is to make the next physical producer obligation non-ambiguous.
-/

import Mathlib.Tactic
import H0mework.Physics.CouplingSources.P288

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Residual threshold / higher-loop correction target -/

/-- The additional inverse-coupling correction needed after the current
two-loop-SM output.  If a future threshold / three-loop / representation
producer supplies this value, then the P288 two-loop inverse correction is
transported to the P287 displayed observational inverse target. -/
def alphaStrongResidualInverseCorrectionNeeded
    (K : Type*) [Field K] : K :=
  alphaStrongDisplayedInverseCorrectionFromCorrectedGUT K -
    alphaStrongTwoLoopSMInverseCorrection K

/-- THEOREM 1: the residual inverse-coupling correction target is exactly
`-89000/128511`. -/
theorem alphaStrongResidualInverseCorrectionNeeded_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongResidualInverseCorrectionNeeded K =
      -((89000 : K) / (128511 : K)) := by
  norm_num [alphaStrongResidualInverseCorrectionNeeded,
    alphaStrongDisplayedInverseCorrectionFromCorrectedGUT,
    alphaStrongDisplayedInverse, alphaStrongTwoLoopSMInverseCorrection,
    alphaStrongTwoLoopSMOutputInverse, alphaGUTInverseSectorNormalized,
    gaugedFundamentalDimension, standardModelSloganSectorCount]

/-- THEOREM 2: the residual correction is negative.  In inverse-coupling
coordinates, the displayed `0.1179` anchor lies above the two-loop `0.109`
output, so its inverse lies lower. -/
theorem alphaStrongResidualInverseCorrectionNeeded_lt_zero
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongResidualInverseCorrectionNeeded K < 0 := by
  rw [alphaStrongResidualInverseCorrectionNeeded_eq]
  norm_num

/-- THEOREM 3: adding the residual correction to the current two-loop-SM
inverse correction gives exactly the displayed inverse-correction target. -/
theorem alphaStrongTwoLoop_plus_residual_eq_displayed_inverse_target
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongTwoLoopSMInverseCorrection K +
      alphaStrongResidualInverseCorrectionNeeded K =
        alphaStrongDisplayedInverseCorrectionFromCorrectedGUT K := by
  unfold alphaStrongResidualInverseCorrectionNeeded
  ring

end StandardModelConstraint
end SaturationMonoid
