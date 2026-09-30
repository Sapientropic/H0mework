import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.Support
import H0mework.Arithmetic.BurnolCarrier.AdditiveFourierPairing
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection

/-! # Fourier landing of the Burnol additive co-sum -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped ENNReal SchwartzMap

noncomputable section

private theorem test_zero_of_quarter_tsupport
    (test : SchwartzMap ℝ ℂ)
    (testSupport : tsupport test ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
    {x : ℝ} (quarterLe : (1 / 4 : ℝ) ≤ |x|) :
    test x = 0 := by
  by_contra nonzero
  have inSupport : x ∈ tsupport test := subset_tsupport test nonzero
  have inside := testSupport inSupport
  exact (not_lt_of_ge quarterLe) (abs_lt.mpr inside)

private theorem source_mul_thetaNonzero_zero
    (test : SchwartzMap ℝ ℂ)
    (testSupport : tsupport test ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
    {u : ℝ} (positive : 0 < u) :
    burnolAdditiveAnnulusSource u *
        coPoissonMuntzThetaNonzero test u⁻¹ = 0 := by
  by_cases sourceZero : burnolAdditiveAnnulusSource u = 0
  · simp [sourceZero]
  · have upper : u < 4 := by
      by_contra notUpper
      have fourLe : 4 ≤ |u| := by
        rw [abs_of_pos positive]
        exact le_of_not_gt notUpper
      exact sourceZero (burnolAdditiveAnnulusSource_zero_of_four_le_abs fourLe)
    have inverseQuarter : (1 / 4 : ℝ) < u⁻¹ := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
      exact (inv_lt_inv₀ (by norm_num) positive).mpr upper
    have termZero (n : {n : ℤ // n ≠ 0}) :
        test (u⁻¹ * (n.1 : ℝ)) = 0 := by
      apply test_zero_of_quarter_tsupport test testSupport
      rw [abs_mul, abs_of_pos (inv_pos.mpr positive)]
      have integerOne : (1 : ℝ) ≤ |(n.1 : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs n.property
      exact le_trans inverseQuarter.le
        (le_mul_of_one_le_right (inv_pos.mpr positive).le integerOne)
    unfold coPoissonMuntzThetaNonzero
    simp_rw [termZero]
    simp

private theorem source_mul_fourierTheta_eq
    (test : SchwartzMap ℝ ℂ)
    (testSupport : tsupport test ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
    {u : ℝ} (positive : 0 < u) :
    burnolAdditiveAnnulusSource u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u =
      test 0 * ((u : ℂ)⁻¹ * burnolAdditiveAnnulusSource u) -
        FourierTransform.fourier test 0 * burnolAdditiveAnnulusSource u := by
  by_cases sourceZero : burnolAdditiveAnnulusSource u = 0
  · simp [sourceZero]
  have thetaZero := source_mul_thetaNonzero_zero test testSupport positive
  have thetaCore : coPoissonMuntzThetaNonzero test u⁻¹ = 0 :=
    (mul_eq_zero.mp thetaZero).resolve_left sourceZero
  have poisson := coPoissonMuntzTheta_fourier_equation test positive
  unfold coPoissonMuntzTheta at poisson
  have uNe : (u : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  simp only [one_div, thetaCore, zero_add, smul_eq_mul] at poisson
  calc
    burnolAdditiveAnnulusSource u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u =
      burnolAdditiveAnnulusSource u *
        ((u : ℂ)⁻¹ * test 0 - FourierTransform.fourier test 0) := by
      congr 1
      apply (mul_left_cancel₀ uNe)
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ uNe, one_mul,
        eq_sub_iff_add_eq]
      calc
        (u : ℂ) * coPoissonMuntzThetaNonzero
              (FourierTransform.fourier test) u +
            (u : ℂ) * FourierTransform.fourier test 0 =
          (u : ℂ) *
            (coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u +
              FourierTransform.fourier test 0) := by ring
        _ = test 0 := poisson.symm
    _ = _ := by ring

private theorem fourier_zero_eq_integral (test : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier test 0 = ∫ x : ℝ, test x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp

private theorem integral_fourier_eq_zero_value (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, FourierTransform.fourier test x) = test 0 := by
  rw [← fourier_zero_eq_integral (FourierTransform.fourier test)]
  simpa using sonine_fourier_fourier_apply test 0

/-- Burnol's additive co-Poisson identity on tests supported in the honest
unscaled Fourier gap. -/
theorem burnolAdditiveFourier_pairing_eq_gapConstant
    (test : SchwartzMap ℝ ℂ)
    (testSupport : tsupport test ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) :
    (∫ t : ℝ, FourierTransform.fourier test t *
        burnolAdditiveCoSum t) =
      burnolAdditiveFourierGapConstant * ∫ t : ℝ, test t := by
  rw [integral_fourier_mul_additiveCoSum_eq,
    tsum_integral_rescaled_eq_positiveTheta]
  have reciprocalIntegrable : IntegrableOn
      (fun u : ℝ => (u : ℂ)⁻¹ * burnolAdditiveAnnulusSource u) (Ioi 0) :=
    burnolAdditiveReciprocalWeightedSource_integrable.integrableOn
  have sourceIntegrable : IntegrableOn burnolAdditiveAnnulusSource (Ioi 0) :=
    burnolAdditiveAnnulusSource_integrable.integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun u positive => source_mul_fourierTheta_eq test testSupport positive),
    integral_sub
      (reciprocalIntegrable.const_mul (test 0))
      (sourceIntegrable.const_mul (FourierTransform.fourier test 0)),
    integral_const_mul, integral_const_mul,
    burnolAdditiveSource_reciprocalMoment_eq_normalization,
    integral_fourier_eq_zero_value,
    fourier_zero_eq_integral]
  unfold burnolAdditiveFourierGapConstant
  ring

/-- The ordinary `L²` Fourier transform of the additive co-sum has the
source-derived Schwartz pairing, with no distributional identity supplied as
a premise. -/
theorem burnolAdditiveFourierL2_toTemperedDistribution_apply
    (test : SchwartzMap ℝ ℂ) :
    ((fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) : 𝓢'(ℝ, ℂ)) test =
      ∫ t : ℝ, FourierTransform.fourier test t *
        burnolAdditiveCoSum t := by
  change (((FourierTransform.fourier burnolAdditiveFullEvenL2 : BurnolL2) :
      𝓢'(ℝ, ℂ)) test) = _
  rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq
    burnolAdditiveFullEvenL2, TemperedDistribution.fourier_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [burnolAdditiveFullEvenL2_coeFn] with t fullEq
  rw [fullEq]
  simp only [smul_eq_mul]

/-- The exact tempered residual between the `L²` Fourier transform and its
source-computed constant mode. -/
def burnolAdditiveFourierGapResidual : 𝓢'(ℝ, ℂ) :=
  ((fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) : 𝓢'(ℝ, ℂ)) -
    burnolAdditiveFourierGapConstant •
      ((volume : Measure ℝ).toTemperedDistribution : 𝓢'(ℝ, ℂ))

/-- The Fourier residual annihilates every Schwartz test supported in the
honest unscaled gap. -/
theorem burnolAdditiveFourierGapResidual_isVanishingOn :
    Distribution.IsVanishingOn burnolAdditiveFourierGapResidual
      (Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) := by
  intro test testSupport
  rw [burnolAdditiveFourierGapResidual,
    sub_apply, smul_apply,
    burnolAdditiveFourierL2_toTemperedDistribution_apply,
    burnolAdditiveFourier_pairing_eq_gapConstant test testSupport]
  rw [MeasureTheory.Measure.toTemperedDistribution_apply
    (volume : Measure ℝ) test]
  simp only [smul_eq_mul, sub_self]

/-- Interval-test annihilation forces the ordinary `L²` representative to
equal the source-computed constant almost everywhere on the open gap. -/
theorem burnolAdditiveFourierL2_ae_eq_gapConstant_on_Ioo :
    ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) →
        (fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) t =
          burnolAdditiveFourierGapConstant := by
  let fourierValue : BurnolL2 := fourierL2 burnolAdditiveFullEvenL2
  let residualFunction : ℝ → ℂ := fun t =>
    fourierValue t - burnolAdditiveFourierGapConstant
  have fourierLocallyIntegrable : LocallyIntegrable
      (fun t : ℝ => fourierValue t) (volume : Measure ℝ) :=
    (MeasureTheory.Lp.memLp fourierValue).locallyIntegrable (by norm_num)
  have constantLocallyIntegrable : LocallyIntegrable
      (fun _ : ℝ => burnolAdditiveFourierGapConstant)
      (volume : Measure ℝ) :=
    continuous_const.locallyIntegrable
  have residualLocallyIntegrable : LocallyIntegrableOn residualFunction
      (Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) (volume : Measure ℝ) := by
    apply LocallyIntegrable.locallyIntegrableOn
    change LocallyIntegrable
      ((fun t : ℝ => fourierValue t) -
        fun _ : ℝ => burnolAdditiveFourierGapConstant) (volume : Measure ℝ)
    exact fourierLocallyIntegrable.sub constantLocallyIntegrable
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
  have complexSupport : tsupport complexTestFunction ⊆
      Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    (tsupport_comp_subset rfl realTest).trans testSupport
  have complexTestSupport : tsupport complexTest ⊆
      Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    change tsupport complexTestFunction ⊆ _
    exact complexSupport
  have vanishes := burnolAdditiveFourierGapResidual_isVanishingOn
    complexTest complexTestSupport
  have testTimesFourierIntegrable : Integrable (fun t : ℝ =>
      complexTest t * fourierValue t) :=
    (complexTest.memLp 2 (volume : Measure ℝ)).integrable_mul
      (MeasureTheory.Lp.memLp fourierValue)
  have constantTimesTestIntegrable : Integrable (fun t : ℝ =>
      burnolAdditiveFourierGapConstant * complexTest t) :=
    complexTest.integrable.const_mul burnolAdditiveFourierGapConstant
  calc
    (∫ t : ℝ, realTest t • residualFunction t) =
        ∫ t : ℝ, complexTest t * fourierValue t -
          burnolAdditiveFourierGapConstant * complexTest t := by
      apply integral_congr_ae
      exact ae_of_all (volume : Measure ℝ) fun t => by
        dsimp only
        rw [complexTest_apply]
        simp only [residualFunction, Complex.real_smul]
        ring
    _ = (∫ t : ℝ, complexTest t * fourierValue t) -
        ∫ t : ℝ, burnolAdditiveFourierGapConstant * complexTest t := by
      rw [integral_sub testTimesFourierIntegrable constantTimesTestIntegrable]
    _ = (∫ t : ℝ, complexTest t * fourierValue t) -
        burnolAdditiveFourierGapConstant * ∫ t : ℝ, complexTest t := by
      rw [integral_const_mul]
    _ = burnolAdditiveFourierGapResidual complexTest := by
      rw [burnolAdditiveFourierGapResidual, sub_apply, smul_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply,
        MeasureTheory.Measure.toTemperedDistribution_apply
          (volume : Measure ℝ) complexTest]
      simp only [smul_eq_mul, fourierValue]
    _ = 0 := vanishes

/-- The actual ordinary Fourier transform is locally constant on the closed
`L²` gap face at the source-derived radius `1 / 4`. -/
theorem burnolAdditiveFourierL2_mem_locallyConstantFace :
    fourierL2 burnolAdditiveFullEvenL2 ∈
      locallyConstantFace burnolUnscaledCommonGapRadius := by
  rw [mem_locallyConstantFace_iff_exists]
  refine ⟨burnolAdditiveFourierGapConstant, ?_⟩
  have intervalAE :
      Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) =ᵐ[(volume : Measure ℝ)]
        Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    MeasureTheory.Ioo_ae_eq_Icc
  have closedIntervalAE : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) →
        (fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) t =
          burnolAdditiveFourierGapConstant := by
    filter_upwards [burnolAdditiveFourierL2_ae_eq_gapConstant_on_Ioo,
      intervalAE] with t openEquality sameInterval
    intro inClosed
    apply openEquality
    change Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) t
    rw [sameInterval]
    exact inClosed
  have constantRestricted : ∀ᵐ t ∂(volume : Measure ℝ).restrict
      (symmetricInterval burnolUnscaledCommonGapRadius),
      (fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) t =
        burnolAdditiveFourierGapConstant := by
    change ∀ᵐ t ∂(volume : Measure ℝ).restrict
      (Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ)), _
    filter_upwards [ae_restrict_of_ae closedIntervalAE,
      ae_restrict_mem measurableSet_Icc] with t equality inClosed
    exact equality inClosed
  apply Lp.ext
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul burnolAdditiveFourierGapConstant
      (intervalConstant burnolUnscaledCommonGapRadius),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval burnolUnscaledCommonGapRadius)
      (fourierL2 burnolAdditiveFullEvenL2),
    constantRestricted]
      with t hsmul hconstant hrestrict hfourier
  calc
    (burnolAdditiveFourierGapConstant •
        intervalConstant burnolUnscaledCommonGapRadius) t =
      burnolAdditiveFourierGapConstant *
        intervalConstant burnolUnscaledCommonGapRadius t := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = burnolAdditiveFourierGapConstant := by rw [hconstant, mul_one]
    _ = (fourierL2 burnolAdditiveFullEvenL2 : BurnolL2) t := hfourier.symm
    _ = restrictToInterval burnolUnscaledCommonGapRadius
        (fourierL2 burnolAdditiveFullEvenL2) t := hrestrict.symm

/-- Actual position/Fourier/even landing of the additive co-sum state. -/
theorem burnolAdditiveFullEvenL2_mem_evenBurnolClosedFace :
    burnolAdditiveFullEvenL2 ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius :=
  burnolAdditiveFullEvenL2_mem_evenBurnolClosedFace_iff.mpr
    burnolAdditiveFourierL2_mem_locallyConstantFace

/-- The terminal exact state: an element of the source-radius physical
carrier together with its same-state nonzero certificate. -/
def burnolAdditiveActualNonzeroPhysicalState :
    {state : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius //
      (state : BurnolL2) ≠ 0} :=
  ⟨⟨burnolAdditiveFullEvenL2,
      burnolAdditiveFullEvenL2_mem_evenBurnolClosedFace⟩,
    burnolAdditiveFullEvenL2_ne_zero⟩

/-- Direct consumer exposing that the terminal subtype contains precisely the
actual Burnol additive full-even realization. -/
theorem burnolAdditiveActualNonzeroPhysicalState_coe :
    ((burnolAdditiveActualNonzeroPhysicalState.1 :
      EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) : BurnolL2) =
        burnolAdditiveFullEvenL2 := rfl

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
