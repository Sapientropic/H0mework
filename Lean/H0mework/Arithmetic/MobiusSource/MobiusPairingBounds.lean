import H0mework.Arithmetic.Muntz.CoPoissonMuntzDirichletSource
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Weighted source control for the exact divisor/Fourier interchange. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace MobiusSourceFourierPairing

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal SchwartzMap
noncomputable section

def rescaled (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  source u * FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)

theorem norm_rescaled_le
    (source : ℝ → ℂ) (atZero : source 0 = 0)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) :
    ‖rescaled source test n u‖ ≤
      ((SchwartzMap.seminorm ℝ 3 0) (FourierTransform.fourier test) /
        (((n + 1 : ℕ) : ℝ) ^ 3)) * (‖source u‖ / |u| ^ 3) := by
  by_cases hu : u = 0
  · simp [rescaled, hu, atZero]
  have positive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have absPositive : 0 < |u| := abs_pos.mpr hu
  have seminorm := SchwartzMap.norm_pow_mul_le_seminorm ℝ
    (FourierTransform.fourier test) 3 (((n + 1 : ℕ) : ℝ) * u)
  have pointBound :
      ‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ ≤
        (SchwartzMap.seminorm ℝ 3 0) (FourierTransform.fourier test) /
          ((((n + 1 : ℕ) : ℝ) ^ 3) * |u| ^ 3) := by
    apply (le_div_iff₀ (mul_pos (pow_pos positive 3) (pow_pos absPositive 3))).2
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos positive, mul_pow, mul_comm] using seminorm
  rw [rescaled, norm_mul]
  calc
    _ ≤ ‖source u‖ *
        ((SchwartzMap.seminorm ℝ 3 0) (FourierTransform.fourier test) /
          ((((n + 1 : ℕ) : ℝ) ^ 3) * |u| ^ 3)) :=
      mul_le_mul_of_nonneg_left pointBound (norm_nonneg _)
    _ = _ := by ring

theorem rescaled_integrable
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (rescaled source test n) := by
  have sourceMeasurable : Measurable (rescaled source test n) :=
    measurable.mul ((FourierTransform.fourier test).continuous.measurable.comp
      (measurable_const.mul measurable_id))
  exact (weighted.const_mul _).mono' sourceMeasurable.aestronglyMeasurable
    (ae_of_all volume (norm_rescaled_le source atZero test n))

theorem summable_integral_norm_rescaled
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖rescaled source test n u‖) := by
  have pSeries : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
    have shifted := (Real.summable_one_div_nat_add_rpow 1 3).mpr (by norm_num)
    refine shifted.congr ?_
    intro n
    rw [abs_of_nonneg (by positivity)]
    norm_num
  let coefficient := (SchwartzMap.seminorm ℝ 3 0) (FourierTransform.fourier test) *
    ∫ u : ℝ, ‖source u‖ / |u| ^ 3
  apply (pSeries.mul_left coefficient).of_nonneg_of_le
  · intro n
    exact integral_nonneg fun _ => norm_nonneg _
  · intro n
    calc
      _ ≤ ∫ u : ℝ,
          ((SchwartzMap.seminorm ℝ 3 0) (FourierTransform.fourier test) /
            (((n + 1 : ℕ) : ℝ) ^ 3)) * (‖source u‖ / |u| ^ 3) :=
        integral_mono (rescaled_integrable source measurable atZero weighted test n).norm
          (weighted.const_mul _) (norm_rescaled_le source atZero test n)
      _ = coefficient * (1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
        rw [integral_const_mul]
        dsimp only [coefficient]
        ring

end
end MobiusSourceFourierPairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
