import H0mework.Versions.Y.Arithmetic.MellinTateSource.Isometry
import H0mework.Arithmetic.Tempered.Remainder
import H0mework.Versions.Y.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartAlgebra

/-! The actual integer-comb remainder as a variable-test L² kernel. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

/-- Reuse the existing quarter-energy realization and the actual Tate map
to realize the original integer-comb remainder at every nonzero scale. -/
def burnolRemainderL2Kernel : SchwartzMap ℝ ℂ →ₗ[ℂ] BurnolL2 :=
  (2 : ℂ) • burnolTateReciprocalL2.toLinearMap.comp
    ((quarterMellinAdditiveEvenRechartLinear (1 / 4 : ℂ)).comp
      (coPoissonQuarterMellinConvergentMap (1 / 4 : ℂ) (by norm_num) (by norm_num)))

theorem burnolRemainderL2Kernel_coeFn (test : SchwartzMap ℝ ℂ) :
    (burnolRemainderL2Kernel test : ℝ → ℂ) =ᵐ[volume]
      fun x => coPoissonMuntzScaleRemainder test |x| := by
  let source := coPoissonQuarterMellinConvergentMap (1 / 4 : ℂ)
    (by norm_num) (by norm_num) test
  let value := quarterMellinAdditiveEvenRechart source
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp value) (quarterMellinAdditiveEvenRechartRaw_memLp source)
    (quarterMellinAdditiveEvenRechart_coeFn source)
  change (((2 : ℂ) • burnolTateReciprocalL2 value : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (2 : ℂ) (burnolTateReciprocalL2 value),
    burnolTateReciprocalL2_coeFn value, pulled, volume.ae_ne (0 : ℝ)]
      with x hscale hvalue hpulled hx
  rw [hscale]
  change (2 : ℂ) * burnolTateReciprocalL2 value x = _
  rw [hvalue, hpulled]
  unfold burnolTateReciprocalRaw quarterMellinAdditiveEvenRechartRaw
    quarterMellinAdditivePositiveRechartRaw
  have positive : 0 < |x| := abs_pos.mpr hx
  have reciprocalSquare : |x⁻¹| ^ (-2 : ℝ) = |x| ^ (2 : Nat) := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, abs_inv, inv_pow, inv_inv]
  rw [reciprocalSquare]
  have argumentPositive : 0 < |x| ^ (2 : Nat) := sq_pos_of_pos positive
  have sourceValue : positiveMellinExtension source.1 (|x| ^ (2 : Nat)) =
      coPoissonMuntzScaleRemainder test |x| := by
    change (if h : 0 < |x| ^ (2 : Nat) then
      source.1 ⟨|x| ^ (2 : Nat), h⟩ else 0) = _
    rw [dif_pos argumentPositive, coPoissonMuntzScaleRemainder, dif_pos positive]
    change clozelTemperedRemainder
      (ClozelEndpointSourceEffect.scaledSchwartzTest (Real.sqrt (|x| ^ (2 : Nat))) _ test) = _
    simp only [Real.sqrt_sq_eq_abs, abs_abs]
  rw [sourceValue]
  simp only [smul_eq_mul, Complex.cpow_neg_one, abs_inv, Complex.ofReal_inv, inv_inv]
  field_simp [abs_ne_zero.mpr hx]

/-- The actual source action on variable Schwartz measurements. Its
integer-comb kernel is fixed; only the source ν varies. -/
def burnolRemainderSourceRead (source : BurnolL2) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • (innerSL ℂ (star source)).toLinearMap.comp burnolRemainderL2Kernel

theorem burnolRemainderSourceRead_integral (source : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead source test =
      (1 / 2 : ℂ) * ∫ x : ℝ, source x * coPoissonMuntzScaleRemainder test |x| := by
  change (1 / 2 : ℂ) * inner ℂ (star source) (burnolRemainderL2Kernel test) = _
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star source, burnolRemainderL2Kernel_coeFn test]
    with x hsource hkernel
  rw [hsource, hkernel]
  simp only [RCLike.inner_apply, Pi.star_apply, starRingEnd_apply, star_star]
  exact mul_comm _ _

/-- Actual half-density dilation of the variable test, on the unchanged
Schwartz carrier. -/
def burnolRemainderSchwartzDilation (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  (Real.exp (shift / 2) : ℂ) •
    ClozelEndpointSourceEffect.scaledSchwartzTest
      (Real.exp shift) (Real.exp_ne_zero shift) test

private theorem remainder_test_dilation (shift : ℝ) (test : SchwartzMap ℝ ℂ)
    {scale : ℝ} (positive : 0 < scale) :
    coPoissonMuntzScaleRemainder (burnolRemainderSchwartzDilation shift test) scale =
      (Real.exp (shift / 2) : ℂ) *
        coPoissonMuntzScaleRemainder test (Real.exp shift * scale) := by
  rw [coPoissonMuntzScaleRemainder, dif_pos positive,
    coPoissonMuntzScaleRemainder, dif_pos (mul_pos (Real.exp_pos shift) positive)]
  unfold burnolRemainderSchwartzDilation ClozelEndpointSourceEffect.scaledSchwartzTest
  rw [map_smul, map_smul]
  change (Real.exp (shift / 2) : ℂ) * _ = (Real.exp (shift / 2) : ℂ) * _
  congr 1
  apply congrArg clozelTemperedRemainder
  ext x
  change test (Real.exp shift * (scale * x)) = test ((Real.exp shift * scale) * x)
  rw [mul_assoc]

/-- Integer-comb evolution is computed before Pa/E projections. -/
theorem burnolRemainderL2Kernel_dilation (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderL2Kernel (burnolRemainderSchwartzDilation shift test) =
      burnolMultiplicativeDilation shift (burnolRemainderL2Kernel test) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [burnolRemainderL2Kernel_coeFn
      (burnolRemainderSchwartzDilation shift test),
    burnolMultiplicativeDilation_coeFn shift (burnolRemainderL2Kernel test),
    qmp.ae (burnolRemainderL2Kernel_coeFn test), volume.ae_ne (0 : ℝ)]
      with x hleft hright hsource hx
  rw [hleft, hright]
  unfold burnolL2RawNormalizedDilation
  rw [hsource, remainder_test_dilation shift test (abs_pos.mpr hx),
    abs_mul, abs_of_pos (Real.exp_pos shift)]

private theorem remainder_fourier (test : SchwartzMap ℝ ℂ)
    {scale : ℝ} (positive : 0 < scale) :
    coPoissonMuntzScaleRemainder (FourierTransform.fourier test) scale =
      (scale : ℂ)⁻¹ * coPoissonMuntzScaleRemainder test scale⁻¹ := by
  have actual := ClozelEndpointSourceEffect.clozelTemperedRemainder_fourier_test
    (ClozelEndpointSourceEffect.scaledSchwartzTest scale⁻¹
      (inv_ne_zero positive.ne') test)
  rw [ClozelEndpointSourceEffect.scaledSchwartzTest_fourier scale⁻¹
    (inv_pos.mpr positive) test] at actual
  simp only [inv_inv, Complex.ofReal_inv, map_smul] at actual
  rw [coPoissonMuntzScaleRemainder, dif_pos positive,
    coPoissonMuntzScaleRemainder, dif_pos (inv_pos.mpr positive)]
  change _ = (scale : ℂ)⁻¹ * _
  rw [← actual]
  change _ = (scale : ℂ)⁻¹ * ((scale : ℂ) * _)
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'), one_mul]

theorem burnolRemainderL2Kernel_fourier (test : SchwartzMap ℝ ℂ) :
    burnolRemainderL2Kernel (FourierTransform.fourier test) =
      burnolTateReciprocalL2 (burnolRemainderL2Kernel test) := by
  have rawMem : MemLp (fun x : ℝ => coPoissonMuntzScaleRemainder test |x|) 2 volume :=
    (Lp.memLp (burnolRemainderL2Kernel test)).ae_eq (burnolRemainderL2Kernel_coeFn test)
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolRemainderL2Kernel test)) rawMem (burnolRemainderL2Kernel_coeFn test)
  apply Lp.ext
  filter_upwards [burnolRemainderL2Kernel_coeFn (FourierTransform.fourier test),
    burnolTateReciprocalL2_coeFn (burnolRemainderL2Kernel test), pulled,
    volume.ae_ne (0 : ℝ)] with x hleft hright hsource hx
  rw [hleft, hright, hsource]
  change coPoissonMuntzScaleRemainder (FourierTransform.fourier test) |x| =
    ((|x| : ℝ) : ℂ)⁻¹ * coPoissonMuntzScaleRemainder test |x⁻¹|
  rw [remainder_fourier test (abs_pos.mpr hx), abs_inv]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
