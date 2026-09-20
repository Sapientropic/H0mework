import H0mework.Physics.JointSources.P376

/-!
# Proposition 377: grand-unification producer normal form

P376 identifies the minimal grand-unification producer kernel as:

* a zero-continuous-free 19-slot certificate; and
* sampled Yukawa clocks.

This file removes the remaining structure wrapper and gives the corresponding
bare existential normal form.  The current unified-formula spine exists iff
there exist a zero-free certificate, a Yukawa `lambda` map, a Yukawa `step` map,
and the single sampling equation tying each discrete Yukawa sigma to
`1-exp(-lambda*step)`.

Boundary: this is the final bookkeeping normal form of the current Lean
unification target.  It is not a construction of the zero-free certificate,
the RG producer, or the physical clock maps.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- The bare producer obligation for the current grand-unification spine. -/
def ExistsZeroFreeSampledYukawaClocks
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ zeroFree :
      ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    ∃ yukawaLambda : YukawaParameter -> ℝ,
      ∃ yukawaStep : YukawaParameter -> ℝ,
        ∀ y : YukawaParameter,
          zeroFree.running.sigma (StandardModelScaleCode.yukawa y) =
            AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)

/-- THEOREM 1: the minimal producer kernel is exactly the bare existential
normal form. -/
theorem minimalProducerKernel_nonempty_iff_existsZeroFreeSampledYukawaClocks :
    Nonempty (MinimalGrandUnificationProducerKernel Index A CKMCarrier) ↔
      ExistsZeroFreeSampledYukawaClocks Index A CKMCarrier := by
  constructor
  · intro h
    rcases h with ⟨M⟩
    exact ⟨M.zeroFree, M.yukawaLambda, M.yukawaStep,
      M.selected_yukawa_sigma_sampled⟩
  · intro h
    rcases h with ⟨zeroFree, yukawaLambda, yukawaStep, hsampled⟩
    exact ⟨{
      zeroFree := zeroFree
      yukawaLambda := yukawaLambda
      yukawaStep := yukawaStep
      selected_yukawa_sigma_sampled := hsampled
    }⟩

/-- THEOREM 2: the current P374 unified-formula spine exists exactly when the
bare zero-free-plus-sampled-clocks producer obligation exists. -/
theorem unifiedFormulaSpine_nonempty_iff_existsZeroFreeSampledYukawaClocks :
    Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) ↔
      ExistsZeroFreeSampledYukawaClocks Index A CKMCarrier := by
  rw [MinimalGrandUnificationProducerKernel.unifiedFormulaSpine_nonempty_iff_minimalProducerKernel_nonempty]
  exact minimalProducerKernel_nonempty_iff_existsZeroFreeSampledYukawaClocks

/-- THEOREM 3: from the bare producer obligation fields one canonically builds
the current P374 unified-formula spine. -/
noncomputable def unifiedFormulaSpineOfZeroFreeSampledYukawaClocks
    (zeroFree :
      ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (yukawaLambda : YukawaParameter -> ℝ)
    (yukawaStep : YukawaParameter -> ℝ)
    (hsampled :
      ∀ y : YukawaParameter,
        zeroFree.running.sigma (StandardModelScaleCode.yukawa y) =
          AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)) :
    StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier :=
  MinimalGrandUnificationProducerKernel.toProducerKernel {
    zeroFree := zeroFree
    yukawaLambda := yukawaLambda
    yukawaStep := yukawaStep
    selected_yukawa_sigma_sampled := hsampled
  } |> GrandUnificationProducerKernel.toUnifiedFormulaSpine

/-- THEOREM 4: the spine built from the bare fields carries the same compact
unified formula receipt as P374. -/
theorem unifiedFormulaSpineOfZeroFreeSampledYukawaClocks_receipt
    (zeroFree :
      ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (yukawaLambda : YukawaParameter -> ℝ)
    (yukawaStep : YukawaParameter -> ℝ)
    (hsampled :
      ∀ y : YukawaParameter,
        zeroFree.running.sigma (StandardModelScaleCode.yukawa y) =
          AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)) :
    let C :=
      unifiedFormulaSpineOfZeroFreeSampledYukawaClocks
        zeroFree yukawaLambda yukawaStep hsampled
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
  exact (unifiedFormulaSpineOfZeroFreeSampledYukawaClocks
    zeroFree yukawaLambda yukawaStep hsampled).unified_formula_spine_receipt

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
