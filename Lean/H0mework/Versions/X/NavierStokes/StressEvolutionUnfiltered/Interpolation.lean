import H0mework.Versions.X.NavierStokes.StressWholeH1.Approximation
import H0mework.Versions.X.NavierStokes.StressWholeH1.Pairing
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativePhysicalTimeInterpolation

open Set Filter MeasureTheory
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing NativeWholeH1Approximation

noncomputable section

theorem inverse_sub (first last : State) :
    inverseGradient (first - last) = inverseGradient first - inverseGradient last := by
  apply lp.ext
  funext wave
  exact smul_sub _ _ _

theorem inverse_norm (value : State) : ‖inverseGradient value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  change ‖(Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • value wave‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact mul_le_of_le_one_left (norm_nonneg _) (inverse_weight_bound wave)

theorem physical_bound (value : wholePhysical) (regular : H1 value) :
    ‖value‖ ^ 2 ≤ ‖inverseGradient value.1‖ * Real.sqrt ((2 * Real.pi) ^ 2 * gradientMass value) := by
  have pairing := real_inner_le_norm (inverseGradient value.1) (gradientValue value regular)
  rw [inverse_gradient_pairing, real_inner_self_eq_norm_sq] at pairing
  rw [← gradientValue_norm_sq value regular, Real.sqrt_sq (norm_nonneg _)]
  exact pairing

theorem gradient_sub_bound (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) :
    gradientMass (first - last) ≤ 2 * (gradientMass first + gradientMass last) := by
  have regular := H1_sub first last firstH1 lastH1
  have difference := pow_le_pow_left₀ (norm_nonneg _)
    (norm_sub_le (gradientValue first firstH1) (gradientValue last lastH1)) 2
  have cross := sq_nonneg (‖gradientValue first firstH1‖ - ‖gradientValue last lastH1‖)
  have estimate : ‖gradientValue first firstH1 - gradientValue last lastH1‖ ^ 2 ≤
      2 * (‖gradientValue first firstH1‖ ^ 2 + ‖gradientValue last lastH1‖ ^ 2) := by nlinarith
  rw [← gradientValue_sub first last firstH1 lastH1 regular, gradientValue_norm_sq,
    gradientValue_norm_sq, gradientValue_norm_sq] at estimate
  have scale : 0 < (2 * Real.pi) ^ 2 := sq_pos_of_pos (by positivity)
  nlinarith

theorem integral_product_square {α : Type*} [MeasurableSpace α] {μ : Measure α} {first last : α → ℝ}
    (firstNonnegative : ∀ᵐ time ∂μ, 0 ≤ first time) (lastNonnegative : ∀ᵐ time ∂μ, 0 ≤ last time)
    (firstLp : MemLp first 2 μ) (lastLp : MemLp last 2 μ) :
    (∫ time, first time * last time ∂μ) ^ 2 ≤
      (∫ time, first time ^ 2 ∂μ) * (∫ time, last time ^ 2 ∂μ) := by
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two firstNonnegative lastNonnegative
    (by simpa only [ENNReal.ofReal_ofNat] using firstLp) (by simpa only [ENNReal.ofReal_ofNat] using lastLp)
  have lower : 0 ≤ ∫ time, first time * last time ∂μ := integral_nonneg_of_ae
    (by filter_upwards [firstNonnegative, lastNonnegative] with time first last; exact mul_nonneg first last)
  have squared := pow_le_pow_left₀ lower holder 2
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at squared
  exact squared

end
end SaturationMonoid.NavierStokes.NativePhysicalTimeInterpolation
