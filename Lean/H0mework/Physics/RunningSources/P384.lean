import H0mework.Physics.RunningSources.P383

/-!
# Proposition 384: RG monotonicity grand-unification receipt

P379-P383 reduce the current Standard-Model unified-formula spine to one
remaining physical producer shape:

* a zero-free 19-slot certificate;
* an RG scale relation placing selected Yukawa scales below the weak endpoint;
* positivity of `fourPi`;
* monotonicity of `g^2` along that relation.

This file packages that reduction as a single receipt object and proves its
normal form exactly: the receipt exists iff the P383 RG-monotonicity corridor
exists.  The receipt carries the P374 unified-formula spine and the P378
primitive producer atoms, so downstream citations no longer need to replay the
P379-P383 chain by hand.

Boundary: this is still certificate-relative.  It does not construct the
physical beta functions, thresholds, representation content, or CKM depth
producer.  It states the exact Lean object those producers must fill.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Grand-unification receipt from the RG monotonicity producer -/

/-- The current "holy grail" receipt shape for the Standard-Model projection.

It keeps the remaining producer (`zeroFree` plus `rg`) visible, but also carries
the already-derived consequences: the gauge weak corridor, the unified formula
spine, and the primitive producer atoms. -/
structure RGMonotonicityGrandUnificationReceipt
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  zeroFree : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier
  rg : SelectedYukawaRGMonotonicityCertificate zeroFree
  gaugeWeakCorridor : SelectedYukawaGaugeCouplingsBoundedByWeak zeroFree
  spine : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier
  primitiveAtoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier

namespace RGMonotonicityGrandUnificationReceipt

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: the receipt forgets to the exact P383 remaining producer. -/
theorem toExistsZeroFreeRGMonotonicityCorridor
    (R : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier :=
  ⟨R.zeroFree, ⟨R.rg⟩⟩

/-- THEOREM 2: the receipt carries the no-continuous-free-parameter surface
through the P374 target receipt. -/
theorem noContinuousFreeParameters
    (R : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :
    NoContinuousFreeParameters
      R.spine.target.sampled.zeroFree.running.pinned.base.constraints :=
  R.spine.target_unified_receipt.1

/-- THEOREM 3: the receipt carries the unified target receipt from P374/P373. -/
theorem targetReceipt
    (R : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :
    NoContinuousFreeParameters
        R.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
      (∀ p : ParameterVector ℝ,
        R.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
          p StandardModelParameter.qcd_theta = 0) ∧
      alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
      (ckmCPDepthSum : ℝ) * R.spine.target.cpRunningSigma =
        cpRawPhaseClaim ℝ ∧
      cpDeltaCPClaim ℝ =
        cpTauProxy ℝ - (ckmCPDepthSum : ℝ) *
          R.spine.target.cpRunningSigma ∧
      alphaStrongTwoLoopSMInverseCorrection ℝ +
          R.spine.target.strongResidualProducer.inverseCorrection =
        alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  R.spine.target_unified_receipt

/-- THEOREM 4: the receipt carries the full unified formula spine receipt:
sampled Yukawa residuals, CKM phase-flow, and the strong residual target. -/
theorem formulaSpineReceipt
    (R : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :
    (alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
        gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
        alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ))) ∧
    (∀ p : ParameterVector ℝ,
      R.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            R.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
              AffineRelaxation.realDecayResidual
                (R.spine.target.sampled.yukawaLambda y)
                ((R.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                    R.spine.target.sampled.zeroFree.selectedSeed y : ℝ) *
                  R.spine.target.sampled.yukawaStep y)) ∧
    AffineRelaxation.unitComplexPhaseWithRate R.spine.target.cpRunningSigma
        (ckmCPDepthSum : ℝ) =
      AffineRelaxation.unitComplexPhase (cpRawPhaseClaim ℝ) ∧
    alphaStrongTwoLoopSMInverseCorrection ℝ +
        R.spine.target.strongResidualProducer.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  R.spine.unified_formula_spine_receipt

/-- THEOREM 5: accepted Yukawa slots are on the sampled continuous relaxation
spine inside the RG-monotonicity receipt. -/
theorem accepted_yukawa_eq_sampled_continuous_residual
    (R : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : R.spine.target.sampled.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter) :
    p (yukawaSlot y) =
      R.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual
          (R.spine.target.sampled.yukawaLambda y)
          ((R.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
              R.spine.target.sampled.zeroFree.selectedSeed y : ℝ) *
            R.spine.target.sampled.yukawaStep y) :=
  R.spine.accepted_yukawa_eq_sampled_continuous_residual p hp y

/-- THEOREM 6: the CKM running phase is still the fixed-rate scalar phase-flow
slice inside the RG-monotonicity receipt. -/
theorem ckm_running_phase_is_fixed_rate_phase_slice
    (R : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) :
    AffineRelaxation.unitComplexPhaseWithRate R.spine.target.cpRunningSigma
        (ckmCPDepthSum : ℝ) =
      AffineRelaxation.unitComplexPhase (cpRawPhaseClaim ℝ) :=
  R.spine.ckm_running_phase_is_fixed_rate_phase_slice

end RGMonotonicityGrandUnificationReceipt

/-- THEOREM 7: the RG monotonicity producer constructs the full grand-unification
receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_exists
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  classical
  intro h
  rcases h with ⟨Z, ⟨RGC⟩⟩
  let hExists : ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier :=
    ⟨Z, ⟨RGC⟩⟩
  rcases unifiedFormulaSpine_nonempty_of_rgMonotonicity hExists with ⟨spine⟩
  rcases primitiveProducerAtoms_nonempty_of_rgMonotonicity hExists with ⟨atoms⟩
  exact
    ⟨{ zeroFree := Z
       rg := RGC
       gaugeWeakCorridor :=
        selectedYukawaGaugeCouplingsBoundedByWeak_of_rgMonotonicity Z RGC
       spine := spine
       primitiveAtoms := atoms }⟩

/-- THEOREM 8: exact normal form.  The current grand-unification receipt exists
iff the P383 zero-free RG-monotonicity corridor exists. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_iff_exists
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) ↔
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier := by
  constructor
  · rintro ⟨R⟩
    exact R.toExistsZeroFreeRGMonotonicityCorridor
  · exact rgMonotonicityGrandUnificationReceipt_nonempty_of_exists

/-- THEOREM 9: the exact normal form still yields the P374 unified-formula
spine. -/
theorem unifiedFormulaSpine_nonempty_iff_rgMonotonicityReceipt_nonempty
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  rintro ⟨R⟩
  exact ⟨R.spine⟩

/-- THEOREM 10: the exact normal form also yields the primitive producer atoms. -/
theorem primitiveProducerAtoms_nonempty_iff_rgMonotonicityReceipt_nonempty
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  rintro ⟨R⟩
  exact ⟨R.primitiveAtoms⟩

end StandardModelConstraint
end SaturationMonoid
