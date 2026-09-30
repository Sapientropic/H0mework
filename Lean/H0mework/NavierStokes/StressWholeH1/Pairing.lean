import H0mework.NavierStokes.StressWholeH1.Mixed
import H0mework.NavierStokes.StressWeakInput.PhysicalPairing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeH1Pairing

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeResolventCompactness NativeWholeResolvent NativeEndpointVelocityCarrier NativeWholeH1Mixed

noncomputable section

theorem multiplier_positive (wave : Wave) : 0 < integerWaveViscousMultiplier wave.1 :=
  mul_pos (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)) (integerWaveNormSq_pos wave.2)

theorem gradient_density (value : wholePhysical) (wave : Wave) :
    curlDensity value.1 wave = (2 * Real.pi) ^ 2 * gradientDensity value wave.1 := by
  have row : euclideanCoordinateRow (wholeVelocity value.1 wave.1) = value.1 wave := by
    apply PiLp.ext
    intro coordinate
    exact wholeVelocity_nonzero value.1 wave coordinate
  rw [curlDensity, gradientDensity, NativeMovingCriticalProduct.amplitude, row, integerWaveViscousMultiplier]
  ring

theorem curl_summable (value : wholePhysical) (regular : H1 value) : Summable (curlDensity value.1) :=
  ((regular.mul_left ((2 * Real.pi) ^ 2)).subtype (fun wave => wave ≠ 0)).congr
    (fun wave => (gradient_density value wave).symm)

theorem h1_of_curl_summable (value : wholePhysical) (regular : Summable (curlDensity value.1)) : H1 value := by
  have normalized : Summable (fun wave : Wave => gradientDensity value wave.1) := by
    apply (regular.mul_left (((2 * Real.pi) ^ 2)⁻¹)).congr
    intro wave
    rw [gradient_density, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero)), one_mul]
  have supported : Function.support (gradientDensity value) ⊆ {wave | wave ≠ 0} := by
    intro wave included
    by_contra zero
    have atZero : wave = 0 := not_ne_iff.mp zero
    subst wave
    simp [gradientDensity, integerWaveNormSq] at included
  exact ((hasSum_subtype_iff_of_support_subset supported).mp normalized.hasSum).summable

def gradientValue (value : wholePhysical) (regular : H1 value) : State :=
  ⟨fun wave => Real.sqrt (integerWaveViscousMultiplier wave.1) • value.1 wave, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply (curl_summable value regular).congr
    intro wave
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (multiplier_positive wave).le]
    rfl⟩

theorem gradientValue_sub (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last)
    (differenceH1 : H1 (first - last)) :
    gradientValue (first - last) differenceH1 = gradientValue first firstH1 - gradientValue last lastH1 := by
  apply lp.ext
  funext wave
  change Real.sqrt (integerWaveViscousMultiplier wave.1) • (first.1 wave - last.1 wave) =
    Real.sqrt (integerWaveViscousMultiplier wave.1) • first.1 wave -
      Real.sqrt (integerWaveViscousMultiplier wave.1) • last.1 wave
  exact smul_sub _ _ _

theorem gradientValue_norm_sq (value : wholePhysical) (regular : H1 value) :
    ‖gradientValue value regular‖ ^ 2 = (2 * Real.pi) ^ 2 * gradientMass value := by
  rw [norm_sq_sum]
  have row (wave : Wave) : ‖gradientValue value regular wave‖ ^ 2 =
      (2 * Real.pi) ^ 2 * gradientDensity value wave.1 := by
    change ‖Real.sqrt (integerWaveViscousMultiplier wave.1) • value.1 wave‖ ^ 2 = _
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (multiplier_positive wave).le]
    exact gradient_density value wave
  simp_rw [row]
  rw [tsum_mul_left]
  congr 1
  apply tsum_subtype_eq_of_support_subset
  intro wave supported
  by_contra zero
  have atZero : wave = 0 := not_ne_iff.mp zero
  subst wave
  simp [gradientDensity, integerWaveNormSq] at supported

theorem inverse_weight_bound (wave : Wave) : (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ ≤ 1 := by
  have multiplier : 1 ≤ integerWaveViscousMultiplier wave.1 := by
    calc
      (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
      _ = (2 * Real.pi) ^ 2 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_integerWaveNormSq wave.1 wave.2) (sq_nonneg _)
  exact inv_le_one_of_one_le₀ (Real.le_sqrt_of_sq_le (by simpa only [one_pow] using multiplier))

def inverseGradient (value : State) : State :=
  ⟨fun wave => (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • value wave, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have summable : Summable (fun wave => ‖value wave‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using value.2.summable (by norm_num)
    refine summable.of_nonneg_of_le (fun wave => sq_nonneg _) (fun wave => ?_)
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact mul_le_of_le_one_left (norm_nonneg _) (inverse_weight_bound wave)⟩

theorem inverse_gradient_pairing (value : State) (test : wholePhysical) (regular : H1 test) :
    inner ℝ (inverseGradient value) (gradientValue test regular) = inner ℝ value test.1 := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro wave
  change inner ℝ ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • value wave)
    (Real.sqrt (integerWaveViscousMultiplier wave.1) • test.1 wave) = _
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul]

end
end SaturationMonoid.NavierStokes.NativeWholeH1Pairing
