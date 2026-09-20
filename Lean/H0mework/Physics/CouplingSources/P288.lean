/-
  Proposition 288: sector-normalized GUT inverse-coupling anchor.

  P287 deliberately kept the strong-coupling RG producer as an opaque field.
  A previous draft tried to lower that producer with

      alpha_GUT^{-1} = (2^7 + dim(SU(7))) / 4,

  but the `/4` denominator was the wrong coordinate: it smuggled in spacetime
  dimension.  The Standard-Model projection's information-side denominator is
  the number of primitive slogan sectors, namely `3`; the numerator uses the
  gauged fundamental dimensions `3 + 2 = 5`, because the two singlet blocks in
  the `3+2+1+1` embedding are gauge-transparent.

  This file therefore records the corrected integer anchor

      alpha_GUT^{-1} = (2^7 + 5) / 3 = 133 / 3,

  plus the current two-loop-SM displayed strong-coupling output

      alpha_s(M_Z) = 109 / 1000,

  and its exact displayed residual against the observational anchor used in
  P287:

      (1179/10000 - 109/1000) / (1179/10000) = 89/1179.

  Boundary: the two-loop value is still a producer output, not a beta-function
  theorem in Lean.  The remaining threshold / three-loop / representation
  corrections are not solved here.
-/

import Mathlib.Tactic
import H0mework.Physics.CouplingSources.P287

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Corrected sector-normalized GUT inverse anchor -/

/-- The number of primitive information sectors used by the Standard-Model
projection.  This is the formal slot for the P177 "three slogan sectors"
denominator. -/
def standardModelSloganSectorCount (K : Type*) [OfNat K 3] : K :=
  (3 : K)

/-- The gauged fundamental block dimension in the compact
`3 + 2 + 1 + 1` embedding.  Only the color `3` and weak `2` blocks contribute
to gauge coupling; the two `1`-dimensional blocks are singlets. -/
def gaugedFundamentalDimension (K : Type*) [OfNat K 5] : K :=
  (5 : K)

/-- The corrected GUT inverse-coupling anchor:
`(2^7 + 5) / 3 = 133/3`. -/
def alphaGUTInverseSectorNormalized (K : Type*) [Field K] : K :=
  (((2 : K) ^ (7 : Nat)) + gaugedFundamentalDimension K) /
    standardModelSloganSectorCount K

/-- THEOREM 1: the sector-normalized GUT inverse coupling is `133/3`. -/
theorem alphaGUTInverseSectorNormalized_eq_133_div_3
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaGUTInverseSectorNormalized K = ((133 : K) / (3 : K)) := by
  norm_num [alphaGUTInverseSectorNormalized, gaugedFundamentalDimension,
    standardModelSloganSectorCount]

/-! ## Two-loop-SM displayed strong-coupling output and residual -/

/-- Current two-loop-SM displayed strong-coupling output from the corrected
GUT anchor.  This is a producer output recorded as a rational displayed value,
not an internal Lean derivation of the RG beta functions. -/
def alphaStrongTwoLoopSMOutput (K : Type*) [Field K] : K :=
  (109 : K) / (1000 : K)

/-- Absolute displayed gap between the P287 observational anchor
`1179/10000` and the two-loop-SM output `109/1000`. -/
def alphaStrongTwoLoopSMDisplayedGap (K : Type*) [Field K] : K :=
  alphaStrongDisplayed K - alphaStrongTwoLoopSMOutput K

/-- Relative displayed error of a predicted strong coupling against the P287
displayed observational anchor. -/
def alphaStrongRelativeErrorToDisplayed (K : Type*) [Field K]
    (predicted : K) : K :=
  (alphaStrongDisplayed K - predicted) / alphaStrongDisplayed K

/-- THEOREM 2: the two-loop-SM displayed output has absolute gap `89/10000`
against `0.1179`. -/
theorem alphaStrongTwoLoopSMDisplayedGap_eq_89_div_10000
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongTwoLoopSMDisplayedGap K = ((89 : K) / (10000 : K)) := by
  norm_num [alphaStrongTwoLoopSMDisplayedGap, alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-- THEOREM 3: the two-loop-SM displayed relative error is exactly
`89/1179`, i.e. about `7.6%`. -/
theorem alphaStrongTwoLoopSMRelativeError_eq_89_div_1179
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongRelativeErrorToDisplayed K (alphaStrongTwoLoopSMOutput K) =
      ((89 : K) / (1179 : K)) := by
  norm_num [alphaStrongRelativeErrorToDisplayed, alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput]

/-- THEOREM 4: the two-loop-SM displayed output is strictly below the P287
displayed observational anchor.  This prevents accidentally reusing the old
"displayed error zero" wording for the corrected anchor. -/
theorem alphaStrongTwoLoopSMOutput_lt_displayed
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongTwoLoopSMOutput K < alphaStrongDisplayed K := by
  norm_num [alphaStrongTwoLoopSMOutput, alphaStrongDisplayed]

/-! ## Inverse-coupling correction targets -/

/-- Inverse of the two-loop-SM displayed output. -/
def alphaStrongTwoLoopSMOutputInverse (K : Type*) [Field K] : K :=
  (1000 : K) / (109 : K)

/-- The inverse-coupling correction from the sector-normalized GUT anchor to
the two-loop-SM displayed output. -/
def alphaStrongTwoLoopSMInverseCorrection (K : Type*) [Field K] : K :=
  alphaStrongTwoLoopSMOutputInverse K - alphaGUTInverseSectorNormalized K

/-- THEOREM 5: the inverse correction needed to reach the two-loop-SM
displayed value from the corrected GUT anchor is `-11497/327`. -/
theorem alphaStrongTwoLoopSMInverseCorrection_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongTwoLoopSMInverseCorrection K =
      -((11497 : K) / (327 : K)) := by
  norm_num [alphaStrongTwoLoopSMInverseCorrection,
    alphaStrongTwoLoopSMOutputInverse, alphaGUTInverseSectorNormalized,
    gaugedFundamentalDimension, standardModelSloganSectorCount]

/-- Inverse of the P287 displayed observational strong-coupling anchor. -/
def alphaStrongDisplayedInverse (K : Type*) [Field K] : K :=
  (10000 : K) / (1179 : K)

/-- The total inverse-coupling correction that would be required to hit the
P287 displayed observational anchor from the corrected GUT anchor.  Future
threshold / three-loop / representation producers must explain the difference
between this target and the two-loop-SM correction above. -/
def alphaStrongDisplayedInverseCorrectionFromCorrectedGUT
    (K : Type*) [Field K] : K :=
  alphaStrongDisplayedInverse K - alphaGUTInverseSectorNormalized K

/-- THEOREM 6: hitting the displayed observational anchor from the corrected
GUT anchor would require inverse correction `-42269/1179`. -/
theorem alphaStrongDisplayedInverseCorrectionFromCorrectedGUT_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongDisplayedInverseCorrectionFromCorrectedGUT K =
      -((42269 : K) / (1179 : K)) := by
  norm_num [alphaStrongDisplayedInverseCorrectionFromCorrectedGUT,
    alphaStrongDisplayedInverse, alphaGUTInverseSectorNormalized,
    gaugedFundamentalDimension, standardModelSloganSectorCount]

end StandardModelConstraint
end SaturationMonoid
