import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory
open scoped ENNReal InnerProductSpace SchwartzMap

noncomputable section

def burnolGaussianRaw (scale x : ℝ) : ℂ :=
  Complex.exp (-((Real.pi * scale * x ^ 2 : ℝ) : ℂ))

theorem burnolGaussianRaw_integrable
    {scale : ℝ} (scalePositive : 0 < scale) :
    Integrable (burnolGaussianRaw scale) := by
  unfold burnolGaussianRaw
  have coefficientPositive : 0 < ((Real.pi * scale : ℝ) : ℂ).re := by
    simp only [ofReal_mul, mul_re, ofReal_re, ofReal_im, mul_zero,
      sub_zero]
    positivity
  convert
    (integrable_cexp_quadratic coefficientPositive (0 : ℂ) (0 : ℂ))
      using 1
  funext x
  congr 1
  push_cast
  ring_nf

theorem burnolGaussianRaw_norm_sq
    (scale x : ℝ) :
    ‖burnolGaussianRaw scale x‖ ^ 2 =
      ‖burnolGaussianRaw (2 * scale) x‖ := by
  rw [burnolGaussianRaw, burnolGaussianRaw,
    Complex.norm_exp, Complex.norm_exp]
  simp only [neg_re, ofReal_re]
  rw [pow_two]
  rw [← Real.exp_add]
  congr 1
  ring

theorem burnolGaussianRaw_memLp
    {scale : ℝ} (scalePositive : 0 < scale) :
    MemLp (burnolGaussianRaw scale) 2 (volume : Measure ℝ) := by
  have continuous : Continuous (burnolGaussianRaw scale) := by
    unfold burnolGaussianRaw
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm
    continuous.aestronglyMeasurable).mpr
  apply (burnolGaussianRaw_integrable (show 0 < 2 * scale by positivity)).norm.congr
  exact ae_of_all volume fun x => (burnolGaussianRaw_norm_sq scale x).symm

def burnolGaussianL2
    (scale : ℝ) (scalePositive : 0 < scale) : BurnolL2 :=
  (burnolGaussianRaw_memLp scalePositive).toLp (burnolGaussianRaw scale)

theorem burnolGaussianL2_coeFn
    (scale : ℝ) (scalePositive : 0 < scale) :
    (burnolGaussianL2 scale scalePositive : ℝ → ℂ) =ᵐ[volume]
      burnolGaussianRaw scale :=
  MemLp.coeFn_toLp (burnolGaussianRaw_memLp scalePositive)

theorem star_burnolGaussianRaw (scale x : ℝ) :
    star (burnolGaussianRaw scale x) = burnolGaussianRaw scale x := by
  simp [burnolGaussianRaw, ← Complex.exp_conj]

theorem inner_burnolGaussianL2_eq_integral
    (scale : ℝ) (scalePositive : 0 < scale) (value : BurnolL2) :
    inner ℂ (burnolGaussianL2 scale scalePositive) value =
      ∫ x : ℝ, value x * burnolGaussianRaw scale x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolGaussianL2_coeFn scale scalePositive] with x gaussianRead
  rw [gaussianRead, RCLike.inner_apply, starRingEnd_apply,
    star_burnolGaussianRaw]

def burnolGaussianReciprocalScale (scale : ℝ) : ℂ :=
  (scale ^ (-(1 / 2 : ℝ)) : ℝ)

theorem burnolGaussianReciprocalScale_eq
    {scale : ℝ} (scalePositive : 0 < scale) :
    burnolGaussianReciprocalScale scale =
      1 / (scale : ℂ) ^ (1 / 2 : ℂ) := by
  rw [burnolGaussianReciprocalScale, Real.rpow_neg scalePositive.le]
  rw [Complex.ofReal_inv, Complex.ofReal_cpow scalePositive.le]
  norm_num

theorem fourier_burnolGaussianRaw
    {scale : ℝ} (scalePositive : 0 < scale) (x : ℝ) :
    FourierTransform.fourier (burnolGaussianRaw scale) x =
      burnolGaussianReciprocalScale scale *
        burnolGaussianRaw scale⁻¹ x := by
  have rawEq : burnolGaussianRaw scale = fun y : ℝ =>
      Complex.exp (-Real.pi * (scale : ℂ) * y ^ 2) := by
    funext y
    rw [burnolGaussianRaw]
    congr 1
    push_cast
    ring
  have transformed := fourier_gaussian_pi
    (b := (scale : ℂ)) (by simpa using scalePositive)
  have atX := congrFun transformed x
  rw [rawEq]
  rw [burnolGaussianReciprocalScale_eq scalePositive]
  simpa [burnolGaussianRaw, div_eq_mul_inv, ofReal_inv,
    ofReal_mul, ofReal_pow, mul_assoc] using atX

theorem integral_fourier_mul_burnolGaussianRaw
    (test : SchwartzMap ℝ ℂ) {scale : ℝ}
    (scalePositive : 0 < scale) :
    (∫ y : ℝ, FourierTransform.fourier test y *
        burnolGaussianRaw scale y) =
      burnolGaussianReciprocalScale scale *
        ∫ x : ℝ, test x * burnolGaussianRaw scale⁻¹ x := by
  have swapped :=
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (.mul ℂ ℂ) (e := Real.fourierChar) (L := innerₗ ℝ)
        (μ := volume) (ν := volume)
        Real.continuous_fourierChar continuous_inner test.integrable
          (burnolGaussianRaw_integrable scalePositive)
  have swapped' :
      (∫ y : ℝ, FourierTransform.fourier test y *
          burnolGaussianRaw scale y) =
        ∫ x : ℝ, test x *
          FourierTransform.fourier (burnolGaussianRaw scale) x := by
    simpa using! swapped
  rw [swapped']
  simp_rw [fourier_burnolGaussianRaw scalePositive]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem inner_burnolGaussianL2_toLp
    (scale : ℝ) (scalePositive : 0 < scale)
    (test : SchwartzMap ℝ ℂ) :
    inner ℂ (burnolGaussianL2 scale scalePositive)
        (test.toLp 2 (volume : Measure ℝ)) =
      ∫ x : ℝ, test x * burnolGaussianRaw scale x := by
  rw [inner_burnolGaussianL2_eq_integral]
  apply integral_congr_ae
  filter_upwards [test.coeFn_toLp 2 (volume : Measure ℝ)] with x testRead
  rw [testRead]

theorem inner_burnolGaussianL2_fourierL2
    (value : BurnolL2) {scale : ℝ} (scalePositive : 0 < scale) :
    inner ℂ (burnolGaussianL2 scale scalePositive) (fourierL2 value) =
      burnolGaussianReciprocalScale scale *
        inner ℂ (burnolGaussianL2 scale⁻¹ (inv_pos.mpr scalePositive)) value := by
  apply DenseRange.induction_on
    (p := fun value : BurnolL2 ↦
      inner ℂ (burnolGaussianL2 scale scalePositive) (fourierL2 value) =
        burnolGaussianReciprocalScale scale *
          inner ℂ (burnolGaussianL2 scale⁻¹ (inv_pos.mpr scalePositive)) value)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top) value
  · apply isClosed_eq
    · exact (innerSL ℂ (burnolGaussianL2 scale scalePositive)).continuous.comp
        fourierL2.continuous
    · exact continuous_const.mul
        (innerSL ℂ
          (burnolGaussianL2 scale⁻¹ (inv_pos.mpr scalePositive))).continuous
  · intro test
    change inner ℂ (burnolGaussianL2 scale scalePositive)
        (FourierTransform.fourier
          (test.toLp 2 (volume : Measure ℝ))) =
      burnolGaussianReciprocalScale scale *
        inner ℂ (burnolGaussianL2 scale⁻¹ (inv_pos.mpr scalePositive))
          (test.toLp 2 (volume : Measure ℝ))
    rw [SchwartzMap.toLp_fourier_eq]
    rw [inner_burnolGaussianL2_toLp,
      inner_burnolGaussianL2_toLp]
    exact integral_fourier_mul_burnolGaussianRaw test scalePositive

theorem burnolGaussian_fourierL2_pairing
    (value : BurnolL2) {scale : ℝ} (scalePositive : 0 < scale) :
    (∫ y : ℝ, (fourierL2 value) y * burnolGaussianRaw scale y) =
      burnolGaussianReciprocalScale scale *
        ∫ x : ℝ, value x * burnolGaussianRaw scale⁻¹ x := by
  rw [← inner_burnolGaussianL2_eq_integral scale scalePositive,
    ← inner_burnolGaussianL2_eq_integral scale⁻¹ (inv_pos.mpr scalePositive)]
  exact inner_burnolGaussianL2_fourierL2 value scalePositive

theorem burnolGaussian_fourierL2_pairing_exp
    (value : BurnolL2) {scale : ℝ} (scalePositive : 0 < scale) :
    (∫ y : ℝ, (fourierL2 value) y *
        Complex.exp (-((Real.pi * scale * y ^ 2 : ℝ) : ℂ))) =
      ((scale ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x : ℝ, value x *
          Complex.exp (-((Real.pi * x ^ 2 / scale : ℝ) : ℂ)) := by
  change (∫ y : ℝ, (fourierL2 value) y * burnolGaussianRaw scale y) = _
  rw [burnolGaussian_fourierL2_pairing value scalePositive]
  apply congrArg (fun z : ℂ ↦
    ((scale ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * z)
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  simp only [burnolGaussianRaw]
  congr 2
  push_cast
  ring

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
