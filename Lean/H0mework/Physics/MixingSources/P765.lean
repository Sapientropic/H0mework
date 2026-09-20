import H0mework.Physics.CouplingSources.P764

/-!
# Proposition 765: physicalized CKM phase closure

P761 produces the CKM phase-depth matrix from the selected Yukawa depth table.
P278 proves that the exact running GUT sigma `2563/193000` sends depth `386`
to the raw Jarlskog phase `5.126`, with complement branch `1.157`.
P764 keeps that CKM matrix inside the physicalized numerical pressure closure.

This file welds those three readings into one certificate:

`CKM matrix -> Jarlskog depth 386 -> exact running sigma -> raw phase -> delta_CP`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification

/-- The CKM phase producer attached to the physicalized SU(7) numerical pressure
closure.

The matrix readout is no longer only a depth sum: multiplying the matrix-level
Jarlskog depth by the exact running sigma gives the raw phase `5.126`, and the
declared CKM phase `1.157` is its complement branch relative to the decimal
turn proxy `6.283`.
-/
structure PhysicalizedCKMPhaseProducerCertificate : Prop where
  physicalized_pressure_closure :
    PhysicalizedNumericalPressureClosureCertificate ℂ
  ckm_matrix_depth_sum :
    ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int)
  ckm_matrix_rows :
    ckmPhaseDepthMatrixRows =
      [[-28, -226, -562], [391, 193, -143], [830, 632, 296]]
  exact_sigma_from_raw_phase :
    sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ / (ckmCPDepthSum : ℚ)
  matrix_depth_times_exact_sigma_raw_phase :
    (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ
  matrix_depth_times_nominal_sigma :
    (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTNominal ℚ =
      cpRawPhaseAtNominalDepth386 ℚ
  matrix_nominal_gap_to_raw_phase :
    cpRawPhaseClaim ℚ -
        (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTNominal ℚ =
      (108 : ℚ) / 1000
  matrix_depth_sigma_correction_closes_gap :
    (ckmJarlskogDepthFromMatrix : ℚ) *
        (sigmaGUTTwoLoopExact ℚ - sigmaGUTNominal ℚ) =
      cpRawPhaseClaim ℚ - cpRawPhaseAtNominalDepth386 ℚ
  delta_cp_complement_from_matrix_phase :
    cpDeltaCPClaim ℚ =
      cpTauProxy ℚ -
        (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTTwoLoopExact ℚ
  delta_cp_abs_error_to_nominal_measurement :
    cpMeasurementNominal ℚ - cpDeltaCPClaim ℚ = (43 : ℚ) / 1000
  delta_cp_percent_error_to_nominal_measurement :
    ((cpMeasurementNominal ℚ - cpDeltaCPClaim ℚ) /
        cpMeasurementNominal ℚ) * (100 : ℚ) = (43 : ℚ) / 12
  nominal_sigma_no_nat_depth_exact_raw_phase :
    ∀ n : Nat,
      (n : ℚ) * sigmaGUTNominal ℚ ≠ cpRawPhaseClaim ℚ

/-- Matrix-level Jarlskog depth times exact running sigma gives raw phase
`5.126`. -/
theorem ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim :
    (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTTwoLoopExact ℚ =
      cpRawPhaseClaim ℚ := by
  have hdepth :
      (ckmJarlskogDepthFromMatrix : ℚ) = (ckmCPDepthSum : ℚ) := by
    exact_mod_cast ckmJarlskogDepthFromMatrix_eq_386
  calc
    (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTTwoLoopExact ℚ =
        (ckmCPDepthSum : ℚ) * sigmaGUTTwoLoopExact ℚ := by
      rw [hdepth]
    _ = cpRawPhaseClaim ℚ := by
      exact ckmCPDepthSum_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim ℚ

/-- Matrix-level Jarlskog depth times nominal sigma gives the nominal raw
phase `5.018`. -/
theorem ckmMatrixDepth_mul_sigmaGUTNominal_eq_nominalPhase :
    (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTNominal ℚ =
      cpRawPhaseAtNominalDepth386 ℚ := by
  have hdepth :
      (ckmJarlskogDepthFromMatrix : ℚ) = (ckmCPDepthSum : ℚ) := by
    exact_mod_cast ckmJarlskogDepthFromMatrix_eq_386
  rw [hdepth]
  rfl

/-- The exact running-sigma correction over nominal sigma closes exactly the
raw-phase gap at the matrix-level Jarlskog depth. -/
theorem ckmMatrixDepth_mul_sigmaCorrection_eq_rawPhaseGap :
    (ckmJarlskogDepthFromMatrix : ℚ) *
        (sigmaGUTTwoLoopExact ℚ - sigmaGUTNominal ℚ) =
      cpRawPhaseClaim ℚ - cpRawPhaseAtNominalDepth386 ℚ := by
  have hdepth :
      (ckmJarlskogDepthFromMatrix : ℚ) = (ckmCPDepthSum : ℚ) := by
    exact_mod_cast ckmJarlskogDepthFromMatrix_eq_386
  calc
    (ckmJarlskogDepthFromMatrix : ℚ) *
        (sigmaGUTTwoLoopExact ℚ - sigmaGUTNominal ℚ) =
        (ckmCPDepthSum : ℚ) *
          (sigmaGUTTwoLoopExact ℚ - sigmaGUTNominal ℚ) := by
      rw [hdepth]
    _ = cpRawPhaseClaim ℚ - cpRawPhaseAtNominalDepth386 ℚ := by
      exact depthSum_mul_sigmaCorrection_eq_rawPhaseGap ℚ

/-- The complement-branch CKM CP phase is read directly from the matrix-level
Jarlskog phase. -/
theorem cpDeltaCPClaim_eq_tauProxy_minus_ckmMatrixPhase :
    cpDeltaCPClaim ℚ =
      cpTauProxy ℚ -
        (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTTwoLoopExact ℚ := by
  rw [ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim]
  exact cpDeltaCPClaim_eq_tauProxy_minus_rawPhaseClaim ℚ

/-- THEOREM: the current physicalized numerical closure produces the CKM phase
chain all the way from the matrix-level Jarlskog depth to `delta_CP = 1.157`. -/
theorem physicalizedCKMPhaseProducerCertificate :
    PhysicalizedCKMPhaseProducerCertificate where
  physicalized_pressure_closure :=
    physicalizedNumericalPressureClosureCertificate (E := ℂ)
  ckm_matrix_depth_sum :=
    ckmJarlskogDepthFromMatrix_eq_386
  ckm_matrix_rows :=
    ckmPhaseDepthMatrixRows_eq
  exact_sigma_from_raw_phase :=
    sigmaGUTTwoLoopExact_eq_rawPhase_per_depth
  matrix_depth_times_exact_sigma_raw_phase :=
    ckmMatrixDepth_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim
  matrix_depth_times_nominal_sigma :=
    ckmMatrixDepth_mul_sigmaGUTNominal_eq_nominalPhase
  matrix_nominal_gap_to_raw_phase := by
    have hnom :
        (ckmJarlskogDepthFromMatrix : ℚ) * sigmaGUTNominal ℚ =
          cpRawPhaseAtNominalDepth386 ℚ :=
      ckmMatrixDepth_mul_sigmaGUTNominal_eq_nominalPhase
    rw [hnom]
    exact cpRawPhaseClaim_minus_nominalDepth386_eq ℚ
  matrix_depth_sigma_correction_closes_gap :=
    ckmMatrixDepth_mul_sigmaCorrection_eq_rawPhaseGap
  delta_cp_complement_from_matrix_phase :=
    cpDeltaCPClaim_eq_tauProxy_minus_ckmMatrixPhase
  delta_cp_abs_error_to_nominal_measurement :=
    cpDeltaCPClaim_abs_error_to_measurement ℚ
  delta_cp_percent_error_to_nominal_measurement :=
    cpDeltaCPClaim_percent_error_to_measurement ℚ
  nominal_sigma_no_nat_depth_exact_raw_phase :=
    no_nat_depth_exact_rawPhaseClaim_with_sigmaGUT

end StandardModelConstraint
end SaturationMonoid
