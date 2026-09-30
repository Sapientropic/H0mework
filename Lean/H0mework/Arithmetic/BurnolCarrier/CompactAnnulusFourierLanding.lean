import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.Support
import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusFourierFamily

/-! # Ordinary Fourier landing of the compact-annulus co-Poisson family -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal SchwartzMap

noncomputable section

theorem burnolCompactAdditiveFourierL2_toTemperedDistribution_apply
    (source : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
    ((fourierL2 (burnolCompactAdditiveL2 source) : BurnolL2) :
        𝓢'(ℝ, ℂ)) test =
      ∫ t : ℝ, FourierTransform.fourier test t *
        burnolCompactAdditiveCoSum source t := by
  change (((FourierTransform.fourier
      (burnolCompactAdditiveL2 source) : BurnolL2) : 𝓢'(ℝ, ℂ)) test) = _
  rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq
    (burnolCompactAdditiveL2 source), TemperedDistribution.fourier_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [burnolCompactAdditiveL2_coeFn source] with t equality
  rw [equality]
  simp only [smul_eq_mul]

def burnolCompactAdditiveFourierGapResidual
    (source : burnolCompactAnnulusSource) : 𝓢'(ℝ, ℂ) :=
  ((fourierL2 (burnolCompactAdditiveL2 source) : BurnolL2) : 𝓢'(ℝ, ℂ)) -
    burnolCompactAdditiveFourierGapConstant source •
      ((volume : Measure ℝ).toTemperedDistribution : 𝓢'(ℝ, ℂ))

theorem burnolCompactAdditiveFourierGapResidual_isVanishingOn
    (source : burnolCompactAnnulusSource) :
    Distribution.IsVanishingOn
      (burnolCompactAdditiveFourierGapResidual source)
      (Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) := by
  intro test testSupport
  rw [burnolCompactAdditiveFourierGapResidual, sub_apply, smul_apply,
    burnolCompactAdditiveFourierL2_toTemperedDistribution_apply,
    burnolCompactAdditiveFourier_pairing_eq_gapConstant
      source test testSupport]
  rw [MeasureTheory.Measure.toTemperedDistribution_apply volume test]
  simp only [smul_eq_mul, sub_self]

theorem burnolCompactAdditiveFourierL2_ae_eq_gapConstant_on_Ioo
    (source : burnolCompactAnnulusSource) :
    ∀ᵐ t ∂volume,
      t ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) →
        (fourierL2 (burnolCompactAdditiveL2 source) : BurnolL2) t =
          burnolCompactAdditiveFourierGapConstant source := by
  let fourierValue : BurnolL2 := fourierL2 (burnolCompactAdditiveL2 source)
  let residualFunction : ℝ → ℂ := fun t =>
    fourierValue t - burnolCompactAdditiveFourierGapConstant source
  have residualLocallyIntegrable : LocallyIntegrableOn residualFunction
      (Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) volume := by
    apply LocallyIntegrable.locallyIntegrableOn
    exact ((MeasureTheory.Lp.memLp fourierValue).locallyIntegrable
      (by norm_num)).sub continuous_const.locallyIntegrable
  have residualZero :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      residualLocallyIntegrable (fun realTest testSmooth testCompact
        testSupport => ?_)
  · filter_upwards [residualZero] with t zeroOnGap
    intro inside
    exact sub_eq_zero.mp (zeroOnGap inside)
  let complexTestFunction : ℝ → ℂ := Complex.ofRealCLM ∘ realTest
  have complexCompact : HasCompactSupport complexTestFunction :=
    testCompact.comp_left rfl
  have complexSmooth := Complex.ofRealCLM.contDiff.comp testSmooth
  let complexTest : SchwartzMap ℝ ℂ :=
    complexCompact.toSchwartzMap complexSmooth
  have complexTest_apply (t : ℝ) : complexTest t = (realTest t : ℂ) := rfl
  have complexTestSupport : tsupport complexTest ⊆
      Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    change tsupport complexTestFunction ⊆ _
    exact (tsupport_comp_subset rfl realTest).trans testSupport
  have vanishes := burnolCompactAdditiveFourierGapResidual_isVanishingOn
    source complexTest complexTestSupport
  have testTimesFourierIntegrable : Integrable (fun t : ℝ =>
      complexTest t * fourierValue t) :=
    (complexTest.memLp 2 volume).integrable_mul
      (MeasureTheory.Lp.memLp fourierValue)
  have constantTimesTestIntegrable : Integrable (fun t : ℝ =>
      burnolCompactAdditiveFourierGapConstant source * complexTest t) :=
    complexTest.integrable.const_mul _
  calc
    (∫ t : ℝ, realTest t • residualFunction t) =
        ∫ t : ℝ, complexTest t * fourierValue t -
          burnolCompactAdditiveFourierGapConstant source * complexTest t := by
      apply integral_congr_ae
      exact ae_of_all volume fun t => by
        change (realTest t : ℂ) *
            (fourierValue t - burnolCompactAdditiveFourierGapConstant source) =
          complexTest t * fourierValue t -
            burnolCompactAdditiveFourierGapConstant source * complexTest t
        rw [complexTest_apply]
        ring
    _ = (∫ t : ℝ, complexTest t * fourierValue t) -
        ∫ t : ℝ,
          burnolCompactAdditiveFourierGapConstant source * complexTest t := by
      rw [integral_sub testTimesFourierIntegrable
        constantTimesTestIntegrable]
    _ = (∫ t : ℝ, complexTest t * fourierValue t) -
        burnolCompactAdditiveFourierGapConstant source *
          ∫ t : ℝ, complexTest t := by rw [integral_const_mul]
    _ = burnolCompactAdditiveFourierGapResidual source complexTest := by
      rw [burnolCompactAdditiveFourierGapResidual, sub_apply, smul_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply,
        MeasureTheory.Measure.toTemperedDistribution_apply volume complexTest]
      simp only [smul_eq_mul, fourierValue]
    _ = 0 := vanishes

theorem burnolCompactAdditiveFourierL2_mem_locallyConstantFace
    (source : burnolCompactAnnulusSource) :
    fourierL2 (burnolCompactAdditiveL2 source) ∈
      locallyConstantFace burnolUnscaledCommonGapRadius := by
  rw [mem_locallyConstantFace_iff_exists]
  refine ⟨burnolCompactAdditiveFourierGapConstant source, ?_⟩
  have intervalAE :
      Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) =ᵐ[volume]
        Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    MeasureTheory.Ioo_ae_eq_Icc
  have closedIntervalAE : ∀ᵐ t ∂volume,
      t ∈ Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) →
        (fourierL2 (burnolCompactAdditiveL2 source) : BurnolL2) t =
          burnolCompactAdditiveFourierGapConstant source := by
    filter_upwards [burnolCompactAdditiveFourierL2_ae_eq_gapConstant_on_Ioo
      source, intervalAE] with t openEquality sameInterval
    intro inClosed
    apply openEquality
    change Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) t
    rw [sameInterval]
    exact inClosed
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul
      (burnolCompactAdditiveFourierGapConstant source)
      (intervalConstant burnolUnscaledCommonGapRadius),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval burnolUnscaledCommonGapRadius)
      (fourierL2 (burnolCompactAdditiveL2 source)),
    ae_restrict_of_ae closedIntervalAE,
    ae_restrict_mem (measurableSet_symmetricInterval
      burnolUnscaledCommonGapRadius)] with t hsmul hconstant hrestrict hfourier ht
  calc
    (burnolCompactAdditiveFourierGapConstant source •
        intervalConstant burnolUnscaledCommonGapRadius :
          Lp ℂ 2 (volume.restrict
            (symmetricInterval burnolUnscaledCommonGapRadius))) t =
      burnolCompactAdditiveFourierGapConstant source *
        intervalConstant burnolUnscaledCommonGapRadius t := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = burnolCompactAdditiveFourierGapConstant source := by
      rw [hconstant, mul_one]
    _ = (fourierL2 (burnolCompactAdditiveL2 source) : BurnolL2) t := by
      symm
      apply hfourier
      simpa [symmetricInterval, burnolUnscaledCommonGapRadius] using ht
    _ = restrictToInterval burnolUnscaledCommonGapRadius
        (fourierL2 (burnolCompactAdditiveL2 source)) t := hrestrict.symm

theorem reflectL2_burnolCompactAdditiveL2
    (source : burnolCompactAnnulusSource) :
    reflectL2 (burnolCompactAdditiveL2 source) =
      burnolCompactAdditiveL2 source := by
  apply Lp.ext
  have valueAtNeg := negMeasurePreserving.quasiMeasurePreserving.ae
    (burnolCompactAdditiveL2_coeFn source)
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (burnolCompactAdditiveL2 source) negMeasurePreserving,
    valueAtNeg, burnolCompactAdditiveL2_coeFn source] with t href hneg hpos
  calc
    reflectL2 (burnolCompactAdditiveL2 source) t =
        burnolCompactAdditiveL2 source (-t) := href
    _ = burnolCompactAdditiveCoSum source (-t) := hneg
    _ = burnolCompactAdditiveCoSum source t :=
      burnolCompactAdditiveCoSum_even source t
    _ = burnolCompactAdditiveL2 source t := hpos.symm

theorem burnolCompactAdditiveL2_mem_evenBurnolClosedFace
    (source : burnolCompactAnnulusSource) :
    burnolCompactAdditiveL2 source ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  exact ⟨⟨burnolCompactAdditiveL2_mem_locallyConstantFace source,
    burnolCompactAdditiveFourierL2_mem_locallyConstantFace source⟩,
    mem_evenL2ClosedFace_iff.mpr (reflectL2_burnolCompactAdditiveL2 source)⟩

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
