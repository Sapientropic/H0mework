import H0mework.Realization.RelaxationFlow.P247
import H0mework.Physics.SourceContracts.P373

/-!
# Proposition 374: standard-model target closure on the unified formula spine

P373 bundles the current Standard-Model grand-unification target receipts:
zero-continuous-free 19-slot surface, `theta_QCD = 0`, integer gauge anchors,
running CKM phase closure, sampled Yukawa residuals, and the strong-coupling
residual target.

This file connects that target certificate back to the already-proved unified
formula spine:

* P242: `X ↦ X + sigma • (Target - X)` as an affine relaxation module law;
* P293: finite sampled same-target relaxation equals the continuous
  fixed-target envelope;
* P247: fixed-rate scalar phase flow.

Boundary: this is still a spine/target certificate.  It does not derive the
physics producers named in P373.  It proves that the current target receipts
sit on the same certified relaxation / sampled-flow / phase-flow algebra rather
than being a disconnected numeric table.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- The grand-unification target certificate equipped with the three certified
spines of the unified equation program.

The `target` field is producer-relative, exactly as in P373.  The three spine
fields are unconditional Lean certificates already proved in the affine
relaxation track. -/
structure StandardModelUnifiedFormulaSpineCertificate
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  target :
    StandardModelGrandUnificationTargetCertificate Index A CKMCarrier
  affineSpine :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate ℝ ℝ
  sampledFlowSpine :
    AffineRelaxation.DiscreteContinuousFixedTargetBridgeCertificate ℝ
  phaseSpine :
    AffineRelaxation.ScalarPhaseFlowWithRateGeneratorCertificate ℂ

namespace StandardModelUnifiedFormulaSpineCertificate

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: the target certificate still carries P373's compact
grand-unification receipt. -/
theorem target_unified_receipt
    (C : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) :
    NoContinuousFreeParameters
        C.target.sampled.zeroFree.running.pinned.base.constraints ∧
      (∀ p : ParameterVector ℝ,
        C.target.sampled.zeroFree.running.pinned.base.constraints p ->
          p StandardModelParameter.qcd_theta = 0) ∧
      alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
      (ckmCPDepthSum : ℝ) * C.target.cpRunningSigma =
        cpRawPhaseClaim ℝ ∧
      cpDeltaCPClaim ℝ =
        cpTauProxy ℝ -
          (ckmCPDepthSum : ℝ) * C.target.cpRunningSigma ∧
      alphaStrongTwoLoopSMInverseCorrection ℝ +
          C.target.strongResidualProducer.inverseCorrection =
        alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  C.target.unified_target_receipt

/-- THEOREM 2: accepted Yukawa slots are explicitly on the sampled continuous
fixed-target relaxation spine. -/
theorem accepted_yukawa_eq_sampled_continuous_residual
    (C : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : C.target.sampled.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter) :
    p (yukawaSlot y) =
      C.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual
          (C.target.sampled.yukawaLambda y)
          ((C.target.sampled.zeroFree.running.pinned.yukawaExponent
              C.target.sampled.zeroFree.selectedSeed y : ℝ) *
            C.target.sampled.yukawaStep y) :=
  C.target.accepted_yukawa_eq_continuous_residual p hp y

/-- THEOREM 3: the CKM running sigma closes the claimed raw phase, now read as
the time argument of the fixed-rate scalar phase-flow spine. -/
theorem ckm_running_phase_is_fixed_rate_phase_slice
    (C : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) :
    AffineRelaxation.unitComplexPhaseWithRate C.target.cpRunningSigma
        (ckmCPDepthSum : ℝ) =
      AffineRelaxation.unitComplexPhase (cpRawPhaseClaim ℝ) := by
  unfold AffineRelaxation.unitComplexPhaseWithRate
  rw [show C.target.cpRunningSigma * (ckmCPDepthSum : ℝ) =
      (ckmCPDepthSum : ℝ) * C.target.cpRunningSigma by ring]
  rw [C.target.running_sigma_closes_raw_cp_phase]

/-- THEOREM 4: the exact running CKM phase also carries the scalar
phase-flow generator equation at that depth. -/
theorem ckm_running_phase_slice_has_generator
    (C : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) :
    HasDerivAt
      (fun τ : ℝ =>
        AffineRelaxation.unitComplexPhaseWithRate C.target.cpRunningSigma τ)
      (((C.target.cpRunningSigma : ℂ) * Complex.I) *
        AffineRelaxation.unitComplexPhaseWithRate C.target.cpRunningSigma
          (ckmCPDepthSum : ℝ))
      (ckmCPDepthSum : ℝ) :=
  C.phaseSpine.phase_derivative C.target.cpRunningSigma (ckmCPDepthSum : ℝ)

/-- THEOREM 5: the strong-coupling residual target remains the P373 producer
receipt inside the unified formula spine certificate. -/
theorem strong_residual_hits_displayed_inverse_target
    (C : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) :
    alphaStrongTwoLoopSMInverseCorrection ℝ +
        C.target.strongResidualProducer.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  C.target.strong_residual_hits_displayed_inverse_target

/-- THEOREM 6: the three standard-model numerical target families all sit on
the same unified formula spine object:

* finite gauge anchors from the 7-facet / SU(7) arithmetic;
* Yukawa slots as sampled fixed-target continuous residuals;
* CKM phase as a fixed-rate scalar phase-flow slice.
-/
theorem unified_formula_spine_receipt
    (C : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) :
    (alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ))) ∧
    (∀ p : ParameterVector ℝ,
      C.target.sampled.zeroFree.running.pinned.base.constraints p ->
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            C.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
              AffineRelaxation.realDecayResidual
                (C.target.sampled.yukawaLambda y)
                ((C.target.sampled.zeroFree.running.pinned.yukawaExponent
                    C.target.sampled.zeroFree.selectedSeed y : ℝ) *
                  C.target.sampled.yukawaStep y)) ∧
    AffineRelaxation.unitComplexPhaseWithRate C.target.cpRunningSigma
        (ckmCPDepthSum : ℝ) =
      AffineRelaxation.unitComplexPhase (cpRawPhaseClaim ℝ) ∧
    alphaStrongTwoLoopSMInverseCorrection ℝ +
        C.target.strongResidualProducer.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ := by
  rcases C.target.three_gauge_integer_anchors with ⟨hem, hweak, hgut⟩
  exact ⟨⟨hem, hweak, hgut⟩,
    (fun p hp y =>
      C.accepted_yukawa_eq_sampled_continuous_residual p hp y),
    C.ckm_running_phase_is_fixed_rate_phase_slice,
    C.strong_residual_hits_displayed_inverse_target⟩

end StandardModelUnifiedFormulaSpineCertificate

/-! ## Canonical spine extension -/

/-- THEOREM 7: any real sampled P372 certificate has a canonical P374 unified
formula-spine extension: P373 supplies the target receipt, and P242/P293/P247
supply the algebraic spine. -/
noncomputable def standardModelUnifiedFormulaSpineCertificateOfRealSampled
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (R : RealSampledStandardModelUnificationCertificate Index A CKMCarrier) :
    StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier where
  target := grandUnificationTargetCertificateOfRealSampled R
  affineSpine :=
    AffineRelaxation.unifiedAffineRelaxationModuleCertificate
      (K := ℝ) (E := ℝ)
  sampledFlowSpine :=
    AffineRelaxation.discreteContinuousFixedTargetBridgeCertificate
      (E := ℝ)
  phaseSpine :=
    AffineRelaxation.scalarPhaseFlowWithRateGeneratorCertificate
      (E := ℂ)

end StandardModelConstraint
end SaturationMonoid
