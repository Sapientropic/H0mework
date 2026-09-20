/-
  Proposition 277: CKM CP phase as an integer-depth phase certificate.

  The proposed calculation says:

    * complexified GUT sigma advances a phase by sigma_GUT each step;
    * fermion phases are integer depths times sigma_GUT;
    * CKM entry phases are integer depth differences times sigma_GUT;
    * a Jarlskog four-product has raw phase 5.126 rad;
    * the reported CKM phase is 1.157 rad, close to the nominal measurement
      1.20 rad.

  This file keeps two things separate.

  First, the 1.157 number is the complement branch `2π - 5.126`, represented
  here with the usual decimal proxy `2π ≈ 6.283`.  It is not the standard
  `[0, 2π)` remainder of 5.126, because 5.126 is already below 2π.

  Second, if sigma_GUT is taken to be exactly P274's `13/1000`, then the raw
  phase `5126/1000` is not an exact integer multiple of sigma_GUT.  The
  integer-depth derivation therefore still owes either an adjusted integer
  sum, a non-exact/renormalized sigma value, or an explicit approximation
  certificate.

  Boundary: this is a phase-arithmetic and certificate-shape file.  It does
  not derive the CKM matrix, Jarlskog invariant, or observed low-energy phase
  from SU(7) representation theory.
-/

import Mathlib.Tactic
import H0mework.Physics.CouplingSources.P276

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Nominal decimal phase values -/

/-- Decimal proxy for one turn: `2π ≈ 6.283`. -/
def cpTauProxy (K : Type*) [Field K] : K :=
  (6283 : K) / (1000 : K)

/-- Claimed raw Jarlskog four-product phase: `5.126` rad. -/
def cpRawPhaseClaim (K : Type*) [Field K] : K :=
  (5126 : K) / (1000 : K)

/-- Claimed effective CKM CP phase: `1.157` rad. -/
def cpDeltaCPClaim (K : Type*) [Field K] : K :=
  (1157 : K) / (1000 : K)

/-- Nominal comparison measurement: `1.20` rad.  This is a comparison target,
not a Lean-verified latest experimental value. -/
def cpMeasurementNominal (K : Type*) [Field K] : K :=
  (6 : K) / (5 : K)

/-- THEOREM 1: the raw phase is below the decimal `2π` proxy. -/
theorem cpRawPhaseClaim_lt_tauProxy
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    cpRawPhaseClaim K < cpTauProxy K := by
  norm_num [cpRawPhaseClaim, cpTauProxy]

/-- THEOREM 2: `1.157` is the complement branch `6.283 - 5.126`. -/
theorem cpDeltaCPClaim_eq_tauProxy_minus_rawPhaseClaim
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    cpDeltaCPClaim K = cpTauProxy K - cpRawPhaseClaim K := by
  norm_num [cpDeltaCPClaim, cpTauProxy, cpRawPhaseClaim]

/-- THEOREM 3: the absolute error between `1.20` and `1.157` is `0.043`. -/
theorem cpDeltaCPClaim_abs_error_to_measurement
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    cpMeasurementNominal K - cpDeltaCPClaim K = (43 : K) / (1000 : K) := by
  norm_num [cpMeasurementNominal, cpDeltaCPClaim]

/-- THEOREM 4: the relative error is `43/1200`, i.e. about `3.58%`. -/
theorem cpDeltaCPClaim_relative_error_to_measurement
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (cpMeasurementNominal K - cpDeltaCPClaim K) /
        cpMeasurementNominal K = (43 : K) / (1200 : K) := by
  norm_num [cpMeasurementNominal, cpDeltaCPClaim]

/-- THEOREM 5: the percentage error is `43/12`, i.e. about `3.58`. -/
theorem cpDeltaCPClaim_percent_error_to_measurement
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ((cpMeasurementNominal K - cpDeltaCPClaim K) /
        cpMeasurementNominal K) * (100 : K) = (43 : K) / (12 : K) := by
  norm_num [cpMeasurementNominal, cpDeltaCPClaim]

/-! ## Integer-depth phase certificate -/

/-- A certificate that a CKM CP phase came from an integer-depth phase sum.

`deltaCP_eq_complement` intentionally records the complement-branch convention.
If a concrete instance wants a different phase convention, it should supply a
different theorem rather than calling the complement branch "modulo". -/
structure CKMCPPhaseIntegerDepthCertificate
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  depthSum : Nat
  sigmaGUT : K
  rawPhase : K
  turn : K
  deltaCP : K
  sigmaGUT_eq_nominal : sigmaGUT = sigmaGUTNominal K
  rawPhase_eq_depth_sigma : rawPhase = (depthSum : K) * sigmaGUT
  deltaCP_eq_complement : deltaCP = turn - rawPhase

namespace CKMCPPhaseIntegerDepthCertificate

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 6: the raw phase is an integer multiple of nominal GUT sigma. -/
theorem rawPhase_eq_depth_sigmaGUTNominal
    (C : CKMCPPhaseIntegerDepthCertificate K) :
    C.rawPhase = (C.depthSum : K) * sigmaGUTNominal K := by
  rw [C.rawPhase_eq_depth_sigma, C.sigmaGUT_eq_nominal]

/-- THEOREM 7: the predicted CP phase is the complement branch of the integer
depth phase. -/
theorem deltaCP_eq_turn_minus_depth_sigmaGUTNominal
    (C : CKMCPPhaseIntegerDepthCertificate K) :
    C.deltaCP = C.turn - (C.depthSum : K) * sigmaGUTNominal K := by
  rw [C.deltaCP_eq_complement, C.rawPhase_eq_depth_sigmaGUTNominal]

end CKMCPPhaseIntegerDepthCertificate

/-! ## Exact-arithmetic diagnostic for the claimed raw phase -/

/-- THEOREM 8: with exact sigma_GUT = 13/1000, no natural-number depth sum
produces the exact raw phase 5.126. -/
theorem no_nat_depth_exact_rawPhaseClaim_with_sigmaGUT
    (n : Nat) :
    (n : ℚ) * sigmaGUTNominal ℚ ≠ cpRawPhaseClaim ℚ := by
  by_cases hle : n ≤ 394
  · have hn : (n : ℚ) ≤ (394 : ℚ) := by
      exact_mod_cast hle
    have hphase_pos : (0 : ℚ) < sigmaGUTNominal ℚ := by
      norm_num [sigmaGUTNominal]
    have hbound :
        (n : ℚ) * sigmaGUTNominal ℚ ≤
          (394 : ℚ) * sigmaGUTNominal ℚ := by
      nlinarith
    have h394 :
        (394 : ℚ) * sigmaGUTNominal ℚ < cpRawPhaseClaim ℚ := by
      norm_num [sigmaGUTNominal, cpRawPhaseClaim]
    exact ne_of_lt (lt_of_le_of_lt hbound h394)
  · have hge : 395 ≤ n := by
      omega
    have hn : (395 : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast hge
    have hphase_pos : (0 : ℚ) < sigmaGUTNominal ℚ := by
      norm_num [sigmaGUTNominal]
    have hbound :
        (395 : ℚ) * sigmaGUTNominal ℚ ≤
          (n : ℚ) * sigmaGUTNominal ℚ := by
      nlinarith
    have h395 :
        cpRawPhaseClaim ℚ < (395 : ℚ) * sigmaGUTNominal ℚ := by
      norm_num [sigmaGUTNominal, cpRawPhaseClaim]
    exact ne_of_gt (lt_of_lt_of_le h395 hbound)

end StandardModelConstraint
end SaturationMonoid
