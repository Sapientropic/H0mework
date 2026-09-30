import H0mework.Arithmetic.MobiusSource.MobiusPairingBounds

/-! Absolute divisor/Fourier interchange and the positive theta read. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace MobiusSourceFourierPairing

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal SchwartzMap
noncomputable section

def original (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  FourierTransform.fourier test t *
    (((n + 1 : ℕ) : ℂ)⁻¹ * source (t / (n + 1 : ℕ)))

theorem original_eq_rescaled
    (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ) (n : ℕ) (t : ℝ) :
    original source test n t = (((n + 1 : ℕ) : ℂ)⁻¹) *
      rescaled source test n (t / (n + 1 : ℕ)) := by
  have positive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  unfold original rescaled
  rw [show ((n + 1 : ℕ) : ℝ) * (t / (n + 1 : ℕ)) = t by field_simp]
  ring

theorem original_integrable
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (original source test n) := by
  have scaled := ((rescaled_integrable source measurable atZero weighted test n).comp_div
    (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)).const_mul (((n + 1 : ℕ) : ℂ)⁻¹)
  exact scaled.congr (ae_of_all volume fun t => (original_eq_rescaled source test n t).symm)

theorem integral_original_eq_rescaled
    (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ t : ℝ, original source test n t) =
      ∫ u : ℝ, rescaled source test n u := by
  have positive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  simp_rw [original_eq_rescaled]
  rw [integral_const_mul, Measure.integral_comp_div, abs_of_pos positive, Complex.real_smul]
  push_cast
  field_simp

theorem integral_norm_original_eq_rescaled
    (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ t : ℝ, ‖original source test n t‖) =
      ∫ u : ℝ, ‖rescaled source test n u‖ := by
  have positive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  simp_rw [original_eq_rescaled, norm_mul, norm_inv, Complex.norm_natCast]
  rw [integral_const_mul, Measure.integral_comp_div
    (fun u : ℝ => ‖rescaled source test n u‖) ((n + 1 : ℕ) : ℝ), abs_of_pos positive]
  simp only [smul_eq_mul]
  field_simp

theorem summable_integral_norm_original
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖original source test n u‖) :=
  (summable_integral_norm_rescaled source measurable atZero weighted test).congr
    fun n => (integral_norm_original_eq_rescaled source test n).symm

theorem integral_forward_eq_rescaledSeries
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, FourierTransform.fourier test t *
      (∑' n : ℕ, (((n + 1 : ℕ) : ℂ)⁻¹) * source (t / (n + 1 : ℕ)))) =
      ∑' n : ℕ, ∫ u : ℝ, rescaled source test n u := by
  calc
    _ = ∫ t : ℝ, ∑' n : ℕ, original source test n t := by
      apply integral_congr_ae
      exact ae_of_all volume fun t => by
        dsimp only
        unfold original
        rw [tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ, original source test n t :=
      (integral_tsum_of_summable_integral_norm
        (original_integrable source measurable atZero weighted test)
        (summable_integral_norm_original source measurable atZero weighted test)).symm
    _ = _ := by
      apply tsum_congr
      exact integral_original_eq_rescaled source test


def paired (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  rescaled source test n u + rescaled source test n (-u)

theorem rescaled_neg_integrable
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun u : ℝ => rescaled source test n (-u)) := by
  convert (rescaled_integrable source measurable atZero weighted test n).comp_mul_left'
    (by norm_num : (-1 : ℝ) ≠ 0) using 1
  funext u
  congr 1
  ring

theorem paired_integrable
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (paired source test n) :=
  (rescaled_integrable source measurable atZero weighted test n).add
    (rescaled_neg_integrable source measurable atZero weighted test n)

theorem integral_rescaled_eq_positivePaired
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ u : ℝ, rescaled source test n u) =
      ∫ u : ℝ in Ioi 0, paired source test n u := by
  have base := rescaled_integrable source measurable atZero weighted test n
  have reflected := rescaled_neg_integrable source measurable atZero weighted test n
  have negative : (∫ u : ℝ in Iic 0, rescaled source test n u) =
      ∫ u : ℝ in Ioi 0, rescaled source test n (-u) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 (rescaled source test n)).symm
  calc
    _ = (∫ u : ℝ in Iic 0, rescaled source test n u) +
        ∫ u : ℝ in Ioi 0, rescaled source test n u := by
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          base.integrableOn base.integrableOn]
    _ = _ := by
      rw [negative, ← integral_add reflected.integrableOn base.integrableOn]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      unfold paired
      exact add_comm _ _

theorem summable_integral_norm_positivePaired
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0, ‖paired source test n u‖) := by
  apply ((summable_integral_norm_rescaled source measurable atZero weighted test).mul_left 2
    ).of_nonneg_of_le
  · intro n
    exact integral_nonneg fun _ => norm_nonneg _
  · intro n
    have base := rescaled_integrable source measurable atZero weighted test n
    have reflected := rescaled_neg_integrable source measurable atZero weighted test n
    calc
      _ ≤ ∫ u : ℝ, ‖paired source test n u‖ :=
        setIntegral_le_integral (paired_integrable source measurable atZero weighted test n).norm
          (ae_of_all _ fun _ => norm_nonneg _)
      _ ≤ ∫ u : ℝ, ‖rescaled source test n u‖ + ‖rescaled source test n (-u)‖ :=
        integral_mono (paired_integrable source measurable atZero weighted test n).norm
          (base.norm.add reflected.norm) (fun u => norm_add_le _ _)
      _ = 2 * ∫ u : ℝ, ‖rescaled source test n u‖ := by
        rw [integral_add base.norm reflected.norm,
          integral_neg_eq_self (fun u : ℝ => ‖rescaled source test n u‖) volume]
        ring

theorem tsum_paired_eq_theta
    (source : ℝ → ℂ) (even : ∀ u, source (-u) = source u)
    (test : SchwartzMap ℝ ℂ) {u : ℝ} (positive : 0 < u) :
    (∑' n : ℕ, paired source test n u) =
      source u * coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u := by
  rw [coPoissonMuntzThetaNonzero_eq_positive_tsum
    (FourierTransform.fourier test) positive.ne', ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold paired rescaled coPoissonMuntzEvenSource
  rw [even]
  simp only [mul_neg]
  ring

theorem integral_forward_eq_positiveTheta
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (even : ∀ u, source (-u) = source u)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, FourierTransform.fourier test t *
      (∑' n : ℕ, (((n + 1 : ℕ) : ℂ)⁻¹) * source (t / (n + 1 : ℕ)))) =
      ∫ u : ℝ in Ioi 0, source u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u := by
  rw [integral_forward_eq_rescaledSeries source measurable atZero weighted test]
  calc
    _ = ∑' n : ℕ, ∫ u : ℝ in Ioi 0, paired source test n u := by
      apply tsum_congr
      exact integral_rescaled_eq_positivePaired source measurable atZero weighted test
    _ = ∫ u : ℝ in Ioi 0, ∑' n : ℕ, paired source test n u :=
      integral_tsum_of_summable_integral_norm
        (fun n => (paired_integrable source measurable atZero weighted test n).integrableOn)
        (summable_integral_norm_positivePaired source measurable atZero weighted test)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact tsum_paired_eq_theta source even test hu

end
end MobiusSourceFourierPairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
