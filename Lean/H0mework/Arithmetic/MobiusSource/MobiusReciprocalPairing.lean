import H0mework.Arithmetic.MobiusSource.MobiusDivisorFourierPairing
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Reciprocal source recharting retains the complete theta zero modes. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace MobiusSourceFourierPairing

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal SchwartzMap
noncomputable section

theorem positiveTheta_integrable
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (even : ∀ u, source (-u) = source u)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun u : ℝ => source u *
      coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u) (Ioi 0) := by
  have pSeries : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
    have shifted := (Real.summable_one_div_nat_add_rpow 1 3).mpr (by norm_num)
    refine shifted.congr ?_
    intro n
    rw [abs_of_nonneg (by positivity)]
    norm_num
  let mass : ℝ := ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 3)
  let S : ℝ := (SchwartzMap.seminorm ℝ 3 0) (FourierTransform.fourier test)
  have thetaMeasurable : Measurable
      (coPoissonMuntzThetaNonzero (FourierTransform.fourier test)) := by
    apply Measurable.tsum
    intro n
    exact (FourierTransform.fourier test).continuous.measurable.comp
      (measurable_id.mul_const _)
  apply (weighted.integrableOn.const_mul (2 * S * mass)).mono'
    (measurable.mul thetaMeasurable).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← tsum_paired_eq_theta source even test hu]
  have bound : ∀ n : ℕ, ‖paired source test n u‖ ≤
      (2 * S * (‖source u‖ / |u| ^ 3)) * (1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
    intro n
    calc
      _ ≤ ‖rescaled source test n u‖ + ‖rescaled source test n (-u)‖ := norm_add_le _ _
      _ ≤ (S / (((n + 1 : ℕ) : ℝ) ^ 3)) * (‖source u‖ / |u| ^ 3) +
          (S / (((n + 1 : ℕ) : ℝ) ^ 3)) * (‖source (-u)‖ / |-u| ^ 3) :=
        add_le_add (norm_rescaled_le source atZero test n u)
          (norm_rescaled_le source atZero test n (-u))
      _ = _ := by
        rw [even, abs_neg]
        ring
  have bounded := tsum_of_norm_bounded
    (pSeries.hasSum.mul_left (2 * S * (‖source u‖ / |u| ^ 3))) bound
  change ‖∑' n : ℕ, paired source test n u‖ ≤ (2 * S * mass) * (‖source u‖ / |u| ^ 3)
  convert bounded using 1
  dsimp only [mass]
  ring


theorem reciprocalThetaJacobian
    (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ)
    {u : ℝ} (positive : 0 < u) :
    (|-1| * u ^ ((-1 : ℝ) - 1)) •
      ((((|u ^ (-1 : ℝ)| : ℝ) : ℂ)⁻¹ * source (u ^ (-1 : ℝ))⁻¹) *
        (coPoissonMuntzTheta test (u ^ (-1 : ℝ)) -
          (((u ^ (-1 : ℝ) : ℝ) : ℂ)⁻¹ * FourierTransform.fourier test 0))) =
      source u * coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u := by
  have poisson := coPoissonMuntzTheta_fourier_equation test positive
  simp only [one_div, smul_eq_mul] at poisson
  rw [Real.rpow_neg_one, inv_inv, abs_of_pos (inv_pos.mpr positive)]
  rw [show ((-1 : ℝ) - 1) = -2 by norm_num, Real.rpow_neg positive.le,
    Real.rpow_two]
  simp only [abs_neg, abs_one, one_mul, Complex.real_smul]
  rw [poisson]
  simp only [coPoissonMuntzTheta]
  push_cast
  field_simp [positive.ne']
  ring

theorem integral_positiveTheta_eq_reciprocal
    (source : ℝ → ℂ) (test : SchwartzMap ℝ ℂ) :
    (∫ u : ℝ in Ioi 0, source u *
      coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u) =
      ∫ u : ℝ in Ioi 0, (((|u| : ℝ) : ℂ)⁻¹ * source u⁻¹) *
        (coPoissonMuntzTheta test u -
          ((u : ℂ)⁻¹ * FourierTransform.fourier test 0)) := by
  calc
    _ = ∫ u : ℝ in Ioi 0, (|-1| * u ^ ((-1 : ℝ) - 1)) •
        ((((|u ^ (-1 : ℝ)| : ℝ) : ℂ)⁻¹ * source (u ^ (-1 : ℝ))⁻¹) *
          (coPoissonMuntzTheta test (u ^ (-1 : ℝ)) -
            (((u ^ (-1 : ℝ) : ℝ) : ℂ)⁻¹ * FourierTransform.fourier test 0))) :=
      setIntegral_congr_fun measurableSet_Ioi fun u hu =>
        (reciprocalThetaJacobian source test hu).symm
    _ = _ := integral_comp_rpow_Ioi
      (fun u : ℝ => (((|u| : ℝ) : ℂ)⁻¹ * source u⁻¹) *
        (coPoissonMuntzTheta test u -
          ((u : ℂ)⁻¹ * FourierTransform.fourier test 0)))
      (p := (-1 : ℝ)) (by norm_num)

theorem reciprocalTheta_integrable
    (source : ℝ → ℂ) (measurable : Measurable source) (atZero : source 0 = 0)
    (even : ∀ u, source (-u) = source u)
    (weighted : Integrable (fun u : ℝ => ‖source u‖ / |u| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun u : ℝ => (((|u| : ℝ) : ℂ)⁻¹ * source u⁻¹) *
      (coPoissonMuntzTheta test u -
        ((u : ℂ)⁻¹ * FourierTransform.fourier test 0))) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_rpow_iff _ (p := (-1 : ℝ)) (by norm_num)).mp
  exact (positiveTheta_integrable source measurable atZero even weighted test).congr_fun
    (fun u hu => (reciprocalThetaJacobian source test hu).symm) measurableSet_Ioi

end
end MobiusSourceFourierPairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
