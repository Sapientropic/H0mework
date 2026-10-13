import H0mework.Versions.V2.Arithmetic.RieszFiniteSource.SourceKernel
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.UnitShellPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ContinuousChannels

open Complex MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFiniteSource
noncomputable section

def channel (direction radius : ℝ) (value : BurnolL2) : BurnolL2 :=
  (Real.sqrt radius : ℂ)⁻¹ •
    burnolMultiplicativeDilation (direction * Real.log radius) value

theorem channel_integrable (direction upper : ℝ) (value : BurnolL2) :
    IntegrableOn (fun radius => channel direction radius value) (Ioc 0 upper) := by
  have regular : ContinuousOn (fun radius => channel direction radius value) (Ioi 0) := by
    apply ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.inv₀
      (fun radius positive => Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.mpr positive).ne')).smul
    exact (burnolMultiplicativeDilation_stronglyContinuous value).comp_continuousOn
      ((Real.continuousOn_log.mono (fun _ positive => ne_of_gt positive)).const_mul direction)
  have boundIntegral : IntegrableOn (fun radius : ℝ => radius ^ (-(1 / 2 : ℝ)) * ‖value‖)
      (Ioc 0 upper) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := upper)
      (by norm_num : -1 < -(1 / 2 : ℝ))).1).mul_const ‖value‖
  apply boundIntegral.mono'
    ((regular.mono (fun _ inside => inside.1)).aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
  simp only [channel, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg radius),
    (burnolMultiplicativeDilation (direction * Real.log radius)).norm_map]
  rw [Real.rpow_neg inside.1.le, ← Real.sqrt_eq_rpow]

def normalization (upper : ℝ) (value : BurnolL2) : BurnolL2 :=
  ∫ radius : ℝ in Ioc 0 upper, channel (-1) radius value

private theorem scaled_character (value : ℂ) (radius : ℝ) (positive : 0 < radius)
    (direction : ℝ) :
    (Real.sqrt radius : ℂ)⁻¹ *
      fullMellinTranslationCharacter value (direction * Real.log radius) =
        (radius : ℂ) ^ (((1 / 2 : ℂ) - value) * direction - 1 / 2) := by
  have squareRoot : Real.sqrt radius = Real.exp (Real.log radius / 2) := by
    rw [Real.exp_half, Real.exp_log positive]
  rw [squareRoot, Complex.ofReal_exp, ← Complex.exp_neg, fullMellinTranslationCharacter,
    ← Complex.exp_add, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne'),
    ← Complex.ofReal_log positive.le]
  congr 1
  push_cast
  ring

theorem kernel_action (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) :
    channel 1 radius (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      (radius : ℂ) ^ (-star coordinate.value) •
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      (Real.sqrt radius : ℂ)⁻¹ • forcingIntegral coordinate (Real.log radius) := by
  unfold channel
  rw [one_mul, original_finite_action, smul_add, smul_smul]
  have scalar := scaled_character (star coordinate.value) radius positive 1
  simp only [one_mul, Complex.ofReal_one, mul_one, sub_sub_cancel_left] at scalar
  rw [scalar]

theorem fourier_kernel_action (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) :
    channel 1 radius (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      (radius : ℂ) ^ (star coordinate.value - 1) •
        fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      (Real.sqrt radius : ℂ)⁻¹ •
        fourierL2 (forcingIntegral coordinate (-Real.log radius)) := by
  have action := fourierL2_burnolMultiplicativeDilation (-Real.log radius)
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  rw [neg_neg] at action
  unfold channel
  rw [one_mul, ← action, original_finite_action, map_add, map_smul, smul_add, smul_smul]
  have scalar := scaled_character (star coordinate.value) radius positive (-1)
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, mul_neg_one] at scalar
  have power : -((1 / 2 : ℂ) - star coordinate.value) - 1 / 2 = star coordinate.value - 1 := by ring
  rw [power] at scalar
  rw [scalar]

private theorem position_forcing_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) :
    IntegrableOn (fun radius : ℝ => (Real.sqrt radius : ℂ)⁻¹ •
      forcingIntegral coordinate (Real.log radius)) (Ioc 0 upper) := by
  have exponent : -1 < (-star coordinate.value).re := by
    simpa only [neg_re, star_def, conj_re] using (neg_lt_neg coordinate.belowOne)
  have diagonal := ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := upper)
    exponent).1).smul_const (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  apply ((channel_integrable 1 upper
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)).sub diagonal).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
  simp only [Pi.sub_apply]
  rw [kernel_action coordinate radius inside.1]
  abel

private theorem fourier_forcing_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) :
    IntegrableOn (fun radius : ℝ => (Real.sqrt radius : ℂ)⁻¹ •
      fourierL2 (forcingIntegral coordinate (-Real.log radius))) (Ioc 0 upper) := by
  have exponent : -1 < (star coordinate.value - 1).re := by
    simp only [sub_re, star_def, conj_re, one_re]
    linarith [coordinate.rightHalf]
  have diagonal := ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := upper)
    exponent).1).smul_const (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
  apply ((channel_integrable 1 upper
    (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))).sub diagonal).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
  simp only [Pi.sub_apply]
  rw [fourier_kernel_action coordinate radius inside.1]
  abel

theorem kernel_integral (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (nonnegative : 0 ≤ upper) :
    (∫ radius : ℝ in Ioc 0 upper,
      channel 1 radius (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      ((upper : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value)) •
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      ∫ radius : ℝ in Ioc 0 upper, (Real.sqrt radius : ℂ)⁻¹ •
        forcingIntegral coordinate (Real.log radius) := by
  have exponent : -1 < (-star coordinate.value).re := by
    simpa only [neg_re, star_def, conj_re] using (neg_lt_neg coordinate.belowOne)
  have diagonal := ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := upper)
    exponent).1).smul_const (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun radius inside => kernel_action coordinate radius inside.1),
    integral_add diagonal (position_forcing_integrable coordinate upper), integral_smul_const]
  congr 2
  rw [← intervalIntegral.integral_of_le nonnegative, integral_cpow (Or.inl exponent)]
  have exponentNe : -star coordinate.value + 1 ≠ 0 := by
    intro equality
    have realPart := congrArg Complex.re equality
    simp only [add_re, neg_re, star_def, conj_re, one_re, zero_re] at realPart
    linarith [coordinate.belowOne]
  simp only [ofReal_zero, zero_cpow exponentNe, sub_zero]
  congr 2 <;> ring

theorem fourier_kernel_integral (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (nonnegative : 0 ≤ upper) :
    (∫ radius : ℝ in Ioc 0 upper,
      channel 1 radius (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))) =
      ((upper : ℂ) ^ (star coordinate.value) / star coordinate.value) •
        fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      ∫ radius : ℝ in Ioc 0 upper, (Real.sqrt radius : ℂ)⁻¹ •
        fourierL2 (forcingIntegral coordinate (-Real.log radius)) := by
  have exponent : -1 < (star coordinate.value - 1).re := by
    simp only [sub_re, star_def, conj_re, one_re]
    linarith [coordinate.rightHalf]
  have diagonal := ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := upper)
    exponent).1).smul_const (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun radius inside => fourier_kernel_action coordinate radius inside.1),
    integral_add diagonal (fourier_forcing_integrable coordinate upper), integral_smul_const]
  congr 2
  rw [← intervalIntegral.integral_of_le nonnegative, integral_cpow (Or.inl exponent)]
  have exponentNe : star coordinate.value - 1 + 1 ≠ 0 := by
    intro equality
    have realPart := congrArg Complex.re equality
    simp only [add_re, sub_re, star_def, conj_re, one_re, zero_re] at realPart
    linarith [coordinate.rightHalf]
  have coordinateNe : star coordinate.value ≠ 0 := by simpa only [sub_add_cancel] using exponentNe
  simp only [ofReal_zero, sub_add_cancel]
  rw [zero_cpow coordinateNe, sub_zero]

theorem channel_pairing (radius : ℝ) (seed test : BurnolL2) :
    inner ℂ (channel (-1) radius seed) test = inner ℂ seed (channel 1 radius test) := by
  unfold channel
  rw [inner_smul_left, inner_smul_right, neg_one_mul, one_mul]
  have flipped := (burnolMultiplicativeDilation (-Real.log radius)).inner_map_eq_flip seed test
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at flipped
  rw [flipped]
  simp

theorem normalization_pairing (upper : ℝ) (seed test : BurnolL2) :
    inner ℂ (normalization upper seed) test =
      inner ℂ seed (∫ radius : ℝ in Ioc 0 upper, channel 1 radius test) := by
  have leftIntegral := congrArg (starRingEnd ℂ)
    (integral_inner (channel_integrable (-1) upper seed) test)
  rw [inner_conj_symm, ← integral_conj] at leftIntegral
  simp only [inner_conj_symm] at leftIntegral
  unfold normalization
  rw [← leftIntegral]
  simp_rw [channel_pairing]
  exact integral_inner (channel_integrable 1 upper test) seed

/-- The continuous compensation has its own arithmetic power and its full original forcing. -/
theorem normalization_kernel (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (nonnegative : 0 ≤ upper) (seed : BurnolL2) :
    inner ℂ (normalization upper seed) (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      ((upper : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value)) *
        inner ℂ seed (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      inner ℂ seed (∫ radius : ℝ in Ioc 0 upper, (Real.sqrt radius : ℂ)⁻¹ •
        forcingIntegral coordinate (Real.log radius)) := by
  rw [normalization_pairing, kernel_integral coordinate upper nonnegative,
    inner_add_right, inner_smul_right]

theorem normalization_fourier_kernel (coordinate : BurnolCompletedMellinCoordinate)
    (upper : ℝ) (nonnegative : 0 ≤ upper) (seed : BurnolL2) :
    inner ℂ (normalization upper seed)
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      ((upper : ℂ) ^ (star coordinate.value) / star coordinate.value) *
        inner ℂ seed (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) +
      inner ℂ seed (∫ radius : ℝ in Ioc 0 upper, (Real.sqrt radius : ℂ)⁻¹ •
        fourierL2 (forcingIntegral coordinate (-Real.log radius))) := by
  rw [normalization_pairing, fourier_kernel_integral coordinate upper nonnegative,
    inner_add_right, inner_smul_right]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ContinuousChannels
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
