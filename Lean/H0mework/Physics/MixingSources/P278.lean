/-
  Proposition 278: running sigma closes the CKM CP integer-depth gap.

  P277 deliberately exposed a mismatch:

    no n : Nat satisfies n * (13/1000) = 5126/1000.

  The intended resolution is that `13/1000` is only the P274 nominal GUT
  proxy.  A running/two-loop GUT sigma can be chosen so that the integer
  Jarlskog depth sum 386 gives the raw phase exactly.

  This file records the arithmetic shape:

    * the Jarlskog four-product depth sum is
      (-226) + (-143) + 562 + 193 = 386;
    * with nominal sigma, 386 steps give 5.018, leaving gap 0.108;
    * the exact running sigma `2563/193000` satisfies
      386 * sigma = 5.126 exactly;
    * the decimal proxy 0.01328 is close but not exact:
      386 * 0.01328 = 5.12608, with error 0.00008;
    * the GUT weak-mixing pin `3/8` can be read as
      dim(SU(7)) / 2^7 = 48 / 128 = 3/8.

  Boundary: this is still arithmetic/certificate shape.  It does not solve the
  RG equations, prove that the physical two-loop RG flow selects this sigma,
  derive the integer depths from SU(7) representation theory, or verify the
  latest experimental CKM phase.
-/

import Mathlib.Tactic
import H0mework.Physics.MixingSources.P277

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## CKM CP integer-depth arithmetic -/

/-- The total integer depth appearing in the proposed Jarlskog four-product
phase sum. -/
def ckmCPDepthSum : Nat := 386

/-- First CKM phase-depth contribution, e.g. `n_s - n_u`. -/
def ckmCPDepthDelta_us : Int := -226

/-- Second CKM phase-depth contribution, e.g. `n_b - n_c`. -/
def ckmCPDepthDelta_cb : Int := -143

/-- Third CKM phase-depth contribution, with conjugation sign already absorbed. -/
def ckmCPDepthDelta_ub_conj : Int := 562

/-- Fourth CKM phase-depth contribution, with conjugation sign already absorbed. -/
def ckmCPDepthDelta_cs_conj : Int := 193

/-- THEOREM 1: the four Jarlskog depth contributions sum to 386. -/
theorem ckmCPDepthDeltas_sum_eq_depthSum :
    ckmCPDepthDelta_us + ckmCPDepthDelta_cb +
        ckmCPDepthDelta_ub_conj + ckmCPDepthDelta_cs_conj =
      (ckmCPDepthSum : Int) := by
  norm_num [ckmCPDepthDelta_us, ckmCPDepthDelta_cb,
    ckmCPDepthDelta_ub_conj, ckmCPDepthDelta_cs_conj, ckmCPDepthSum]

/-- Raw phase produced by depth 386 with the nominal P274 sigma 13/1000. -/
def cpRawPhaseAtNominalDepth386 (K : Type*) [Field K] : K :=
  (ckmCPDepthSum : K) * sigmaGUTNominal K

/-- THEOREM 2: nominal sigma gives raw phase 5.018 at depth 386. -/
theorem cpRawPhaseAtNominalDepth386_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    cpRawPhaseAtNominalDepth386 K = (5018 : K) / (1000 : K) := by
  norm_num [cpRawPhaseAtNominalDepth386, ckmCPDepthSum, sigmaGUTNominal]

/-- THEOREM 3: the nominal-depth gap to the claimed raw phase is 0.108. -/
theorem cpRawPhaseClaim_minus_nominalDepth386_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    cpRawPhaseClaim K - cpRawPhaseAtNominalDepth386 K =
      (108 : K) / (1000 : K) := by
  norm_num [cpRawPhaseClaim, cpRawPhaseAtNominalDepth386, ckmCPDepthSum,
    sigmaGUTNominal]

/-! ## Exact running sigma and decimal proxy -/

/-- Exact running/two-loop sigma required for depth 386 to hit raw phase 5.126.

This is `5.126 / 386 = 2563/193000`, not the rounded decimal proxy 0.01328. -/
def sigmaGUTTwoLoopExact (K : Type*) [Field K] : K :=
  (2563 : K) / (193000 : K)

/-- Rounded decimal proxy for the exact running sigma: 0.01328. -/
def sigmaGUTTwoLoopDecimalProxy (K : Type*) [Field K] : K :=
  (83 : K) / (6250 : K)

/-- THEOREM 4: exact running sigma is raw phase divided by depth 386. -/
theorem sigmaGUTTwoLoopExact_eq_rawPhase_per_depth :
    sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ / (ckmCPDepthSum : ℚ) := by
  norm_num [sigmaGUTTwoLoopExact, cpRawPhaseClaim, ckmCPDepthSum]

/-- THEOREM 5: with exact running sigma, depth 386 gives raw phase 5.126. -/
theorem ckmCPDepthSum_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (ckmCPDepthSum : K) * sigmaGUTTwoLoopExact K = cpRawPhaseClaim K := by
  norm_num [ckmCPDepthSum, sigmaGUTTwoLoopExact, cpRawPhaseClaim]

/-- THEOREM 6: the exact running correction over nominal sigma is 54/193000. -/
theorem sigmaGUTTwoLoopExact_minus_nominal_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    sigmaGUTTwoLoopExact K - sigmaGUTNominal K =
      (54 : K) / (193000 : K) := by
  norm_num [sigmaGUTTwoLoopExact, sigmaGUTNominal]

/-- THEOREM 7: multiplying the exact running correction by depth 386 gives
the full raw-phase gap 0.108. -/
theorem depthSum_mul_sigmaCorrection_eq_rawPhaseGap
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (ckmCPDepthSum : K) *
        (sigmaGUTTwoLoopExact K - sigmaGUTNominal K) =
      cpRawPhaseClaim K - cpRawPhaseAtNominalDepth386 K := by
  norm_num [ckmCPDepthSum, sigmaGUTTwoLoopExact, sigmaGUTNominal,
    cpRawPhaseClaim, cpRawPhaseAtNominalDepth386]

/-- THEOREM 8: the decimal proxy exceeds the exact value by 1/4,825,000. -/
theorem sigmaGUTTwoLoopDecimalProxy_minus_exact_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    sigmaGUTTwoLoopDecimalProxy K - sigmaGUTTwoLoopExact K =
      (1 : K) / (4825000 : K) := by
  norm_num [sigmaGUTTwoLoopDecimalProxy, sigmaGUTTwoLoopExact]

/-- THEOREM 9: using rounded 0.01328 at depth 386 overshoots raw phase by
0.00008. -/
theorem depthSum_mul_decimalProxy_minus_rawPhaseClaim_eq
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (ckmCPDepthSum : K) * sigmaGUTTwoLoopDecimalProxy K -
        cpRawPhaseClaim K = (1 : K) / (12500 : K) := by
  norm_num [ckmCPDepthSum, sigmaGUTTwoLoopDecimalProxy, cpRawPhaseClaim]

/-! ## SU(7) information-ratio weak-mixing arithmetic -/

/-- Lie-algebra dimension proxy for SU(7): `7^2 - 1`. -/
def su7GaugeFreedomDimension (K : Type*) [Ring K] : K :=
  (7 : K) ^ (2 : Nat) - 1

/-- Seven binary facets give `2^7` information states. -/
def sevenFacetInformationStateCount (K : Type*) [Semiring K] : K :=
  (2 : K) ^ (7 : Nat)

/-- The proposed GUT weak-mixing information ratio. -/
def gutWeakMixingInformationRatio (K : Type*) [Field K] : K :=
  su7GaugeFreedomDimension K / sevenFacetInformationStateCount K

/-- THEOREM 10: `dim SU(7) = 7^2 - 1 = 48`. -/
theorem su7GaugeFreedomDimension_eq_48
    (K : Type*) [Ring K] :
    su7GaugeFreedomDimension K = (48 : K) := by
  norm_num [su7GaugeFreedomDimension]

/-- THEOREM 11: seven binary facets give `2^7 = 128` states. -/
theorem sevenFacetInformationStateCount_eq_128
    (K : Type*) [Semiring K] :
    sevenFacetInformationStateCount K = (128 : K) := by
  norm_num [sevenFacetInformationStateCount]

/-- THEOREM 12: `dim(SU(7)) / 2^7 = 48/128 = 3/8`. -/
theorem gutWeakMixingInformationRatio_eq_threeEighths
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    gutWeakMixingInformationRatio K = threeEighths K := by
  norm_num [gutWeakMixingInformationRatio, su7GaugeFreedomDimension,
    sevenFacetInformationStateCount, threeEighths]

end StandardModelConstraint
end SaturationMonoid
