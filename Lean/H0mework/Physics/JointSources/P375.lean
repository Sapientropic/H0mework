import H0mework.Physics.SourceContracts.P374

/-!
# Proposition 375: grand-unification producer reduction

P374 proves that a real sampled Standard-Model unification certificate extends
to the current unified-formula spine certificate.  This file records the
converse bookkeeping theorem: a P374 spine certificate contains exactly such a
real sampled certificate as its remaining producer kernel.

In other words, after P371-P374 the extra algebraic spines, exact running CKM
sigma, and strong residual target no longer add new producer degrees of
freedom.  Existence of the current grand-unification spine certificate is
equivalent to existence of the real sampled zero-free 19-slot certificate.

Boundary: this is a reduction theorem.  It does not construct the real sampled
certificate itself.  It makes the remaining producer obligation precise.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- The exact producer kernel that remains after P371-P374.

Everything else in the P374 unified-formula spine is canonical or already
unconditional once this real sampled 19-slot certificate is supplied. -/
abbrev GrandUnificationProducerKernel
    (Index A CKMCarrier : Type*) [AddCommGroup A] :=
  RealSampledStandardModelUnificationCertificate Index A CKMCarrier

namespace GrandUnificationProducerKernel

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: a producer kernel canonically builds the P374 unified-formula
spine certificate. -/
noncomputable def toUnifiedFormulaSpine
    (R : GrandUnificationProducerKernel Index A CKMCarrier) :
    StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier :=
  standardModelUnifiedFormulaSpineCertificateOfRealSampled R

/-- THEOREM 2: a P374 unified-formula spine exposes its exact remaining
producer kernel by projection. -/
def ofUnifiedFormulaSpine
    (C : StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) :
    GrandUnificationProducerKernel Index A CKMCarrier :=
  C.target.sampled

/-- THEOREM 3: producer -> spine -> producer is definitionally the same
producer. -/
theorem producer_roundTrip
    (R : GrandUnificationProducerKernel Index A CKMCarrier) :
    ofUnifiedFormulaSpine (toUnifiedFormulaSpine R) = R := rfl

/-- THEOREM 4: existence of the current P374 unified-formula spine certificate
is exactly existence of the real sampled producer kernel. -/
theorem unifiedFormulaSpine_nonempty_iff_producerKernel_nonempty :
    Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) ↔
      Nonempty (GrandUnificationProducerKernel Index A CKMCarrier) := by
  constructor
  · intro h
    rcases h with ⟨C⟩
    exact ⟨ofUnifiedFormulaSpine C⟩
  · intro h
    rcases h with ⟨R⟩
    exact ⟨toUnifiedFormulaSpine R⟩

/-- THEOREM 5: the zero-continuous-free 19-slot surface is already part of the
producer kernel; the P374 spine adds no new continuous parameter. -/
theorem producerKernel_no_continuous_free_parameters
    (R : GrandUnificationProducerKernel Index A CKMCarrier) :
    NoContinuousFreeParameters R.zeroFree.running.pinned.base.constraints :=
  R.toStandardModelUnificationCertificate.no_continuous_free_parameters

/-- THEOREM 6: the producer kernel is exactly where the real sampled Yukawa
clock lives.  The P374 spine transports this field; it does not invent it. -/
theorem producerKernel_selected_yukawa_sigma_sampled
    (R : GrandUnificationProducerKernel Index A CKMCarrier)
    (y : YukawaParameter) :
    R.zeroFree.running.sigma (StandardModelScaleCode.yukawa y) =
      AffineRelaxation.realDecayRate (R.yukawaLambda y) (R.yukawaStep y) :=
  R.selected_yukawa_sigma_sampled y

/-- THEOREM 7: every accepted Yukawa slot supplied by the producer kernel is
already a continuous residual sample. -/
theorem producerKernel_accepted_yukawa_eq_continuous_residual
    (R : GrandUnificationProducerKernel Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : R.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter) :
    p (yukawaSlot y) =
      R.zeroFree.running.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual (R.yukawaLambda y)
          ((R.zeroFree.running.pinned.yukawaExponent
              R.zeroFree.selectedSeed y : ℝ) * R.yukawaStep y) :=
  R.accepted_yukawa_eq_continuous_residual p hp y

/-- THEOREM 8: the P374 compact target receipt is a consequence of the producer
kernel and the already-certified canonical spines/targets. -/
theorem producerKernel_gives_unified_target_receipt
    (R : GrandUnificationProducerKernel Index A CKMCarrier) :
    NoContinuousFreeParameters
        (toUnifiedFormulaSpine R).target.sampled.zeroFree.running.pinned.base.constraints ∧
      (∀ p : ParameterVector ℝ,
        (toUnifiedFormulaSpine R).target.sampled.zeroFree.running.pinned.base.constraints p ->
          p StandardModelParameter.qcd_theta = 0) ∧
      alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
      (ckmCPDepthSum : ℝ) * (toUnifiedFormulaSpine R).target.cpRunningSigma =
        cpRawPhaseClaim ℝ ∧
      cpDeltaCPClaim ℝ =
        cpTauProxy ℝ -
          (ckmCPDepthSum : ℝ) * (toUnifiedFormulaSpine R).target.cpRunningSigma ∧
      alphaStrongTwoLoopSMInverseCorrection ℝ +
          (toUnifiedFormulaSpine R).target.strongResidualProducer.inverseCorrection =
        alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  (toUnifiedFormulaSpine R).target_unified_receipt

/-- THEOREM 9: the P374 unified formula-spine receipt is likewise just the
producer kernel transported through the canonical spine extension. -/
theorem producerKernel_gives_unified_formula_spine_receipt
    (R : GrandUnificationProducerKernel Index A CKMCarrier) :
    (alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ))) ∧
    (∀ p : ParameterVector ℝ,
      (toUnifiedFormulaSpine R).target.sampled.zeroFree.running.pinned.base.constraints p ->
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            (toUnifiedFormulaSpine R).target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
              AffineRelaxation.realDecayResidual
                ((toUnifiedFormulaSpine R).target.sampled.yukawaLambda y)
                (((toUnifiedFormulaSpine R).target.sampled.zeroFree.running.pinned.yukawaExponent
                    (toUnifiedFormulaSpine R).target.sampled.zeroFree.selectedSeed y : ℝ) *
                  (toUnifiedFormulaSpine R).target.sampled.yukawaStep y)) ∧
    AffineRelaxation.unitComplexPhaseWithRate
        (toUnifiedFormulaSpine R).target.cpRunningSigma
        (ckmCPDepthSum : ℝ) =
      AffineRelaxation.unitComplexPhase (cpRawPhaseClaim ℝ) ∧
    alphaStrongTwoLoopSMInverseCorrection ℝ +
        (toUnifiedFormulaSpine R).target.strongResidualProducer.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  (toUnifiedFormulaSpine R).unified_formula_spine_receipt

end GrandUnificationProducerKernel

end StandardModelConstraint
end SaturationMonoid
