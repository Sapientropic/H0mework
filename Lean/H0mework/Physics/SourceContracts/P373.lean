import H0mework.Physics.MixingSources.P278
import H0mework.Physics.JointSources.P372

/-!
# Proposition 373: Grand-unification target closure certificate

P371/P372 package the finite gauge core and the zero-continuous-free 19-slot
surface.  P277/P278 separately package the CKM CP phase arithmetic: nominal
`sigma_GUT = 13/1000` does *not* close the raw phase, while the exact running
sigma `2563/193000` does.  P289 separately packages the remaining strong
inverse-coupling correction target.

This file joins those receipts without pretending to solve the physics
producers.  It proves that a real sampled Standard-Model unification
certificate can be extended by:

* the exact running CKM sigma;
* a threshold / higher-loop correction producer whose value is the P289 target;

and then the central arithmetic closure statements all live in one object.

Boundary: this is still producer-relative.  It does not derive the selected
zero-free seed, SU(7) representation content, CKM depths, Higgs thresholds, or
the beta functions.  It closes the Lean bookkeeping seam between the current
unification certificates.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Strong-coupling producer target -/

/-- A producer-side certificate for the still-missing strong-coupling
threshold / higher-loop / representation correction.

The important part is that this structure does not hide the remaining
obligation: it names the producer's correction and requires it to equal the
P289 target. -/
structure StrongCouplingResidualProducerCertificate
    (K : Type*) [Field K] where
  inverseCorrection : K
  inverseCorrection_eq_needed :
    inverseCorrection = alphaStrongResidualInverseCorrectionNeeded K

namespace StrongCouplingResidualProducerCertificate

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 1: a producer matching the P289 residual target transports the
current two-loop inverse correction to the displayed inverse target. -/
theorem corrected_inverse_hits_displayed_target
    (C : StrongCouplingResidualProducerCertificate K) :
    alphaStrongTwoLoopSMInverseCorrection K + C.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT K := by
  rw [C.inverseCorrection_eq_needed]
  exact alphaStrongTwoLoop_plus_residual_eq_displayed_inverse_target K

/-- THEOREM 2: the required residual correction is the exact rational target
already isolated by P289. -/
theorem inverseCorrection_eq_exact_target
    (C : StrongCouplingResidualProducerCertificate K) :
    C.inverseCorrection = -((89000 : K) / (128511 : K)) := by
  rw [C.inverseCorrection_eq_needed]
  exact alphaStrongResidualInverseCorrectionNeeded_eq K

end StrongCouplingResidualProducerCertificate

/-! ## Grand-unification closure target -/

/-- The current grand-unification target certificate.

It bundles the real sampled 19-slot/gauge unification certificate with the two
remaining arithmetic closure producers that had been living in side files:

* exact running sigma for CKM CP phase closure;
* the exact strong-coupling inverse residual target.

This is intentionally a target/closure certificate, not a full physics
derivation. -/
structure StandardModelGrandUnificationTargetCertificate
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  sampled :
    RealSampledStandardModelUnificationCertificate Index A CKMCarrier
  cpRunningSigma : ℝ
  cpRunningSigma_eq_exact :
    cpRunningSigma = sigmaGUTTwoLoopExact ℝ
  strongResidualProducer :
    StrongCouplingResidualProducerCertificate ℝ

namespace StandardModelGrandUnificationTargetCertificate

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 3: the accepted 19-slot constraint surface is still a singleton in
the grand-unification target certificate. -/
theorem no_continuous_free_parameters
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    NoContinuousFreeParameters
      C.sampled.zeroFree.running.pinned.base.constraints :=
  C.sampled.toStandardModelUnificationCertificate.no_continuous_free_parameters

/-- THEOREM 4: accepted solutions still have `theta_QCD = 0`. -/
theorem accepted_thetaQCD_zero
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : C.sampled.zeroFree.running.pinned.base.constraints p) :
    p StandardModelParameter.qcd_theta = 0 :=
  C.sampled.toStandardModelUnificationCertificate.accepted_thetaQCD_zero p hp

/-- THEOREM 5: accepted solutions' declared GUT weak-mixing observable still
equals the structural-card ratio. -/
theorem accepted_gutWeakMixingSquared_eq_structuralCards
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : C.sampled.zeroFree.running.pinned.base.constraints p) :
    C.sampled.zeroFree.running.pinned.gutWeakMixingSquared p =
      gutWeakMixingFromStructuralCards ℝ :=
  C.sampled.toStandardModelUnificationCertificate
    |>.accepted_gutWeakMixingSquared_eq_structuralCards p hp

/-- THEOREM 6: the nominal `13/1000` sigma cannot exactly produce the claimed
raw CKM phase from any natural-number depth.  The target certificate keeps this
failure visible rather than hiding it. -/
theorem nominal_sigma_no_nat_depth_exact_rawPhase
    (_C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier)
    (n : Nat) :
    (n : ℚ) * sigmaGUTNominal ℚ ≠ cpRawPhaseClaim ℚ :=
  no_nat_depth_exact_rawPhaseClaim_with_sigmaGUT n

/-- THEOREM 7: the Jarlskog four-product integer depth deltas sum to `386`. -/
theorem ckm_depth_deltas_sum_eq_386
    (_C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    ckmCPDepthDelta_us + ckmCPDepthDelta_cb +
        ckmCPDepthDelta_ub_conj + ckmCPDepthDelta_cs_conj =
      (ckmCPDepthSum : Int) :=
  ckmCPDepthDeltas_sum_eq_depthSum

/-- THEOREM 8: with the exact running sigma, depth `386` gives the claimed raw
phase exactly. -/
theorem running_sigma_closes_raw_cp_phase
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    (ckmCPDepthSum : ℝ) * C.cpRunningSigma = cpRawPhaseClaim ℝ := by
  rw [C.cpRunningSigma_eq_exact]
  exact ckmCPDepthSum_mul_sigmaGUTTwoLoopExact_eq_rawPhaseClaim ℝ

/-- THEOREM 9: the reported CKM phase is the complement branch of the exact
running-depth raw phase, using the decimal turn proxy from P277. -/
theorem deltaCP_eq_tauProxy_minus_running_depth
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    cpDeltaCPClaim ℝ =
      cpTauProxy ℝ - (ckmCPDepthSum : ℝ) * C.cpRunningSigma := by
  rw [C.running_sigma_closes_raw_cp_phase]
  exact cpDeltaCPClaim_eq_tauProxy_minus_rawPhaseClaim ℝ

/-- THEOREM 10: the displayed CKM comparison error remains the P277 exact
`43/1200` relative error. -/
theorem deltaCP_relative_error_to_measurement
    (_C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    (cpMeasurementNominal ℝ - cpDeltaCPClaim ℝ) /
        cpMeasurementNominal ℝ = (43 : ℝ) / (1200 : ℝ) :=
  cpDeltaCPClaim_relative_error_to_measurement ℝ

/-- THEOREM 11: the strong residual producer, if supplied at the P289 target,
closes the displayed inverse-coupling correction target. -/
theorem strong_residual_hits_displayed_inverse_target
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    alphaStrongTwoLoopSMInverseCorrection ℝ +
        C.strongResidualProducer.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  C.strongResidualProducer.corrected_inverse_hits_displayed_target

/-- THEOREM 12: the same certificate still carries the three integer gauge
anchors from P371/P372. -/
theorem three_gauge_integer_anchors
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) :=
  C.sampled.toStandardModelUnificationCertificate.three_gauge_integer_anchors

/-- THEOREM 13: accepted Yukawa slots remain sampled continuous residuals in
the grand-unification target certificate. -/
theorem accepted_yukawa_eq_continuous_residual
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : C.sampled.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter) :
    p (yukawaSlot y) =
      C.sampled.zeroFree.running.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual (C.sampled.yukawaLambda y)
          ((C.sampled.zeroFree.running.pinned.yukawaExponent
              C.sampled.zeroFree.selectedSeed y : ℝ) *
            C.sampled.yukawaStep y) :=
  C.sampled.accepted_yukawa_eq_continuous_residual p hp y

/-- THEOREM 14: one compact receipt for the current unification target:
singleton 19-slot surface, `theta_QCD = 0`, integer gauge anchors, exact
running CKM closure, complement-branch phase, and the strong inverse residual
producer target. -/
theorem unified_target_receipt
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    NoContinuousFreeParameters
        C.sampled.zeroFree.running.pinned.base.constraints ∧
      (∀ p : ParameterVector ℝ,
        C.sampled.zeroFree.running.pinned.base.constraints p ->
          p StandardModelParameter.qcd_theta = 0) ∧
      alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
      (ckmCPDepthSum : ℝ) * C.cpRunningSigma = cpRawPhaseClaim ℝ ∧
      cpDeltaCPClaim ℝ =
        cpTauProxy ℝ - (ckmCPDepthSum : ℝ) * C.cpRunningSigma ∧
      alphaStrongTwoLoopSMInverseCorrection ℝ +
          C.strongResidualProducer.inverseCorrection =
        alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ := by
  rcases C.three_gauge_integer_anchors with ⟨hem, hweak, hgut⟩
  exact ⟨C.no_continuous_free_parameters,
    (fun p hp => C.accepted_thetaQCD_zero p hp),
    hem, hweak, hgut, C.running_sigma_closes_raw_cp_phase,
    C.deltaCP_eq_tauProxy_minus_running_depth,
    C.strong_residual_hits_displayed_inverse_target⟩

end StandardModelGrandUnificationTargetCertificate

/-! ## Canonical target extension -/

/-- THEOREM 15: any real sampled P372 unification certificate has a canonical
grand-unification target extension: use the P278 exact running CKM sigma and
the P289 residual inverse-coupling target.

This object is still a target certificate.  It should not be read as a
threshold / CKM / representation-content calculation. -/
noncomputable def grandUnificationTargetCertificateOfRealSampled
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (R : RealSampledStandardModelUnificationCertificate Index A CKMCarrier) :
    StandardModelGrandUnificationTargetCertificate Index A CKMCarrier where
  sampled := R
  cpRunningSigma := sigmaGUTTwoLoopExact ℝ
  cpRunningSigma_eq_exact := rfl
  strongResidualProducer :=
    { inverseCorrection := alphaStrongResidualInverseCorrectionNeeded ℝ
      inverseCorrection_eq_needed := rfl }

end StandardModelConstraint
end SaturationMonoid
