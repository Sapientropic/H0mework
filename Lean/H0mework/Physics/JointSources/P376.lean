import H0mework.Physics.JointSources.P375

/-!
# Proposition 376: minimal grand-unification producer kernel

P375 reduces the current P374 unified-formula spine certificate to the real
sampled Standard-Model producer kernel.  This file removes one more layer of
bookkeeping: the P372 gauge core inside that kernel is canonical once the
zero-free 19-slot certificate is supplied.

The remaining producer obligation is therefore exactly:

* a real-valued zero-continuous-free 19-slot Standard-Model certificate; and
* for each Yukawa slot, a real sampled clock whose one-step rate equals the
  running sigma at that discrete Yukawa scale.

Everything else currently in P371-P375 is transported canonically from those
fields.  Boundary: this still does not construct the zero-free certificate or
the Yukawa clocks; it proves that no additional grand-unification producer
degree of freedom is hidden in the present Lean spine.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Minimal producer kernel -/

/-- The minimal producer kernel left after P371-P375.

Compared with `GrandUnificationProducerKernel`, this structure does not carry a
separate gauge-core field.  P371/P372 supply that core canonically from the
scalar carrier once `zeroFree` exists. -/
structure MinimalGrandUnificationProducerKernel
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  zeroFree :
    ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier
  yukawaLambda : YukawaParameter -> ℝ
  yukawaStep : YukawaParameter -> ℝ
  selected_yukawa_sigma_sampled :
    ∀ y : YukawaParameter,
      zeroFree.running.sigma (StandardModelScaleCode.yukawa y) =
        AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)

namespace MinimalGrandUnificationProducerKernel

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: a minimal kernel canonically extends to the P375 producer
kernel by adding the canonical P371/P372 gauge core. -/
noncomputable def toProducerKernel
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier) :
    GrandUnificationProducerKernel Index A CKMCarrier where
  toStandardModelUnificationCertificate :=
    standardModelUnificationCertificateOfZeroFree M.zeroFree
  yukawaLambda := M.yukawaLambda
  yukawaStep := M.yukawaStep
  selected_yukawa_sigma_sampled := M.selected_yukawa_sigma_sampled

/-- THEOREM 2: any P375 producer kernel exposes this minimal kernel by
forgetting the canonical/unnecessary gauge-core field. -/
def ofProducerKernel
    (R : GrandUnificationProducerKernel Index A CKMCarrier) :
    MinimalGrandUnificationProducerKernel Index A CKMCarrier where
  zeroFree := R.zeroFree
  yukawaLambda := R.yukawaLambda
  yukawaStep := R.yukawaStep
  selected_yukawa_sigma_sampled := R.selected_yukawa_sigma_sampled

/-- THEOREM 3: minimal -> producer -> minimal is definitionally the same
minimal producer obligation. -/
theorem minimal_roundTrip
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier) :
    ofProducerKernel (toProducerKernel M) = M := rfl

/-- THEOREM 4: existence of the P375 producer kernel is exactly existence of
the minimal kernel.  The separate gauge core contributes no producer-side
existence content. -/
theorem producerKernel_nonempty_iff_minimalProducerKernel_nonempty :
    Nonempty (GrandUnificationProducerKernel Index A CKMCarrier) ↔
      Nonempty (MinimalGrandUnificationProducerKernel Index A CKMCarrier) := by
  constructor
  · intro h
    rcases h with ⟨R⟩
    exact ⟨ofProducerKernel R⟩
  · intro h
    rcases h with ⟨M⟩
    exact ⟨toProducerKernel M⟩

/-- THEOREM 5: the current P374 unified-formula spine exists exactly when the
minimal producer kernel exists. -/
theorem unifiedFormulaSpine_nonempty_iff_minimalProducerKernel_nonempty :
    Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) ↔
      Nonempty (MinimalGrandUnificationProducerKernel Index A CKMCarrier) := by
  rw [GrandUnificationProducerKernel.unifiedFormulaSpine_nonempty_iff_producerKernel_nonempty]
  exact producerKernel_nonempty_iff_minimalProducerKernel_nonempty

/-- THEOREM 6: the minimal kernel already carries the zero-continuous-free
19-slot surface. -/
theorem minimalKernel_no_continuous_free_parameters
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier) :
    NoContinuousFreeParameters M.zeroFree.running.pinned.base.constraints :=
  M.zeroFree.no_continuous_free_parameters

/-- THEOREM 7: the minimal kernel is exactly where the sampled Yukawa clock is
owed.  The gauge, target, and formula-spine certificates only transport it. -/
theorem minimalKernel_selected_yukawa_sigma_sampled
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier)
    (y : YukawaParameter) :
    M.zeroFree.running.sigma (StandardModelScaleCode.yukawa y) =
      AffineRelaxation.realDecayRate (M.yukawaLambda y) (M.yukawaStep y) :=
  M.selected_yukawa_sigma_sampled y

/-- THEOREM 8: accepted Yukawa slots from the minimal kernel are sampled
continuous residuals after canonical extension. -/
theorem minimalKernel_accepted_yukawa_eq_continuous_residual
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier)
    (p : ParameterVector ℝ)
    (hp : M.zeroFree.running.pinned.base.constraints p)
    (y : YukawaParameter) :
    p (yukawaSlot y) =
      M.zeroFree.running.pinned.yukawaAmplitude y *
        AffineRelaxation.realDecayResidual (M.yukawaLambda y)
          ((M.zeroFree.running.pinned.yukawaExponent
              M.zeroFree.selectedSeed y : ℝ) * M.yukawaStep y) :=
  (toProducerKernel M).producerKernel_accepted_yukawa_eq_continuous_residual
    p hp y

/-- THEOREM 9: from the minimal kernel, the whole current P374 formula-spine
receipt follows by canonical extension. -/
theorem minimalKernel_gives_unified_formula_spine_receipt
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier) :
    (alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ))) ∧
    (∀ p : ParameterVector ℝ,
      (GrandUnificationProducerKernel.toUnifiedFormulaSpine
          (toProducerKernel M)).target.sampled.zeroFree.running.pinned.base.constraints p ->
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            (GrandUnificationProducerKernel.toUnifiedFormulaSpine
              (toProducerKernel M)).target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
              AffineRelaxation.realDecayResidual
                ((GrandUnificationProducerKernel.toUnifiedFormulaSpine
                  (toProducerKernel M)).target.sampled.yukawaLambda y)
                (((GrandUnificationProducerKernel.toUnifiedFormulaSpine
                    (toProducerKernel M)).target.sampled.zeroFree.running.pinned.yukawaExponent
                    (GrandUnificationProducerKernel.toUnifiedFormulaSpine
                      (toProducerKernel M)).target.sampled.zeroFree.selectedSeed y : ℝ) *
                  (GrandUnificationProducerKernel.toUnifiedFormulaSpine
                    (toProducerKernel M)).target.sampled.yukawaStep y)) ∧
    AffineRelaxation.unitComplexPhaseWithRate
        (GrandUnificationProducerKernel.toUnifiedFormulaSpine
          (toProducerKernel M)).target.cpRunningSigma
        (ckmCPDepthSum : ℝ) =
      AffineRelaxation.unitComplexPhase (cpRawPhaseClaim ℝ) ∧
    alphaStrongTwoLoopSMInverseCorrection ℝ +
        (GrandUnificationProducerKernel.toUnifiedFormulaSpine
          (toProducerKernel M)).target.strongResidualProducer.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  (toProducerKernel M).producerKernel_gives_unified_formula_spine_receipt

end MinimalGrandUnificationProducerKernel

end StandardModelConstraint
end SaturationMonoid
