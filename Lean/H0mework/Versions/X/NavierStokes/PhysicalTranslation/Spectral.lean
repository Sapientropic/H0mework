import H0mework.Versions.X.NavierStokes.PhysicalReadout.Gradient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
open scoped ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeSpatialTranslation

open MeasureTheory Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientRawSourceCore
open NativePhysicalFourier NativePhysicalGradient

noncomputable section

def frequency (direction : Fin 3) (wave : IntegerWavevector) : ℝ := 2 * Real.pi * (wave direction : ℝ)

def phase (direction : Fin 3) (time : ℝ) (wave : IntegerWavevector) : ℂ :=
  Complex.exp (Complex.I * ((time * frequency direction wave : ℝ) : ℂ))

theorem phase_norm (direction : Fin 3) (time : ℝ) (wave : IntegerWavevector) : ‖phase direction time wave‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

theorem phase_zero (direction : Fin 3) (wave : IntegerWavevector) : phase direction 0 wave = 1 := by
  simp [phase]

theorem phase_add (direction : Fin 3) (first second : ℝ) (wave : IntegerWavevector) :
    phase direction (first + second) wave = phase direction first wave * phase direction second wave := by
  simp only [phase, add_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

def translate (direction : Fin 3) (time : ℝ) (state : ScalarSequence) : ScalarSequence :=
  ⟨fun wave => phase direction time wave * state wave,
    (lp.memℓp state).mono' (fun wave => by rw [norm_mul, phase_norm, one_mul])⟩

theorem translate_zero (direction : Fin 3) (state : ScalarSequence) : translate direction 0 state = state := by
  apply lp.ext
  funext wave
  simp [translate, phase_zero]

theorem multiplier_eq (direction : Fin 3) (wave : IntegerWavevector) :
    multiplier wave direction = Complex.I * (frequency direction wave : ℂ) := by
  simp only [multiplier, frequency, Complex.ofReal_mul,
    complexWavevector]
  ring

theorem phase_hasDerivAt (direction : Fin 3) (wave : IntegerWavevector) (time : ℝ) :
    HasDerivAt (fun actual => phase direction actual wave)
      (multiplier wave direction * phase direction time wave) time := by
  have scalar := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time
    ((hasDerivAt_id time).mul_const (frequency direction wave))
  have generated := (scalar.const_mul Complex.I).cexp
  convert generated using 1
  · rfl
  · rw [multiplier_eq]
    simp only [phase, one_mul, Function.comp_apply, id_eq, Complex.ofRealCLM_apply]
    ring

theorem phase_quotient_bound (direction : Fin 3) (wave : IntegerWavevector) (time : ℝ) :
    ‖(time : ℂ)⁻¹ * (phase direction time wave - 1)‖ ≤ ‖multiplier wave direction‖ := by
  by_cases zero : time = 0
  · subst time
    simp
  · have nonzero : ‖time‖ ≠ 0 := norm_ne_zero_iff.mpr zero
    rw [norm_mul, norm_inv, Complex.norm_real]
    calc
      _ ≤ ‖time‖⁻¹ * ‖time * frequency direction wave‖ :=
        mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le (inv_nonneg.mpr (norm_nonneg _))
      _ = ‖frequency direction wave‖ := by rw [norm_mul, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
      _ = _ := by rw [multiplier_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]

theorem translate_add (direction : Fin 3) (first second : ℝ) (state : ScalarSequence) :
    translate direction (first + second) state = translate direction first (translate direction second state) := by
  apply lp.ext
  funext wave
  change phase direction (first + second) wave * state wave = _
  rw [phase_add]
  exact mul_assoc _ _ _

private theorem quotient_bound (direction : Fin 3) (state : ScalarSequence) (time : ℝ) (wave : IntegerWavevector) :
    ‖(time⁻¹ • (translate direction time state - state) : ScalarSequence) wave‖ ≤
      ‖multiplier wave direction‖ * ‖state wave‖ := by
  have value : (time⁻¹ • (translate direction time state - state) : ScalarSequence) wave =
      ((time : ℂ)⁻¹ * (phase direction time wave - 1)) * state wave := by
    change time⁻¹ • (phase direction time wave * state wave - state wave) = _
    simp [Complex.real_smul, sub_mul, mul_assoc]
  rw [value, norm_mul]
  exact mul_le_mul_of_nonneg_right (phase_quotient_bound direction wave time) (norm_nonneg _)

/-- The already generated square-summable spectral jet differentiates the complete translation orbit. -/
theorem translate_hasDerivAt_zero (direction : Fin 3) (state derivative : ScalarSequence)
    (generated : ∀ wave, derivative wave = multiplier wave direction * state wave) :
    HasDerivAt (fun time => translate direction time state) derivative 0 := by
  let quotient (time : ℝ) : ScalarSequence := time⁻¹ • (translate direction time state - state)
  have rowLimit (wave : IntegerWavevector) :
      Tendsto (fun time => quotient time wave) (𝓝[≠] 0) (𝓝 (derivative wave)) := by
    have row := (phase_hasDerivAt direction wave 0).mul_const (state wave)
    rw [phase_zero, mul_one, ← generated wave] at row
    change Tendsto (fun time => time⁻¹ • (phase direction time wave * state wave - state wave)) _ _
    simpa only [zero_add, phase_zero, one_mul] using row.tendsto_slope_zero
  have summable : Summable (fun wave => ‖derivative wave‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp derivative).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have bound (time : ℝ) (wave : IntegerWavevector) :
      ‖‖(quotient time - derivative) wave‖ ^ 2‖ ≤ 4 * ‖derivative wave‖ ^ 2 := by
    have quotientBound := quotient_bound direction state time wave
    rw [← norm_mul, ← generated wave] at quotientBound
    have subtraction : ‖(quotient time - derivative) wave‖ ≤ 2 * ‖derivative wave‖ :=
      (norm_sub_le _ _).trans (by change ‖quotient time wave‖ + ‖derivative wave‖ ≤ _; linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg ((quotient time - derivative) wave), norm_nonneg (derivative wave)]
  have sumLimit : Tendsto (fun time => ∑' wave, ‖(quotient time - derivative) wave‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have generatedLimit := tendsto_tsum_of_dominated_convergence (summable.mul_left 4)
      (fun wave => by
        change Tendsto (fun time => ‖quotient time wave - derivative wave‖ ^ 2) _ (𝓝 (0 : ℝ))
        simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using ((rowLimit wave).sub_const (derivative wave)).norm.pow 2)
      (Filter.Eventually.of_forall bound)
    simpa only [tsum_zero] using generatedLimit
  have normSquare (time : ℝ) : ‖quotient time - derivative‖ ^ 2 =
      ∑' wave, ‖(quotient time - derivative) wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (quotient time - derivative)
  have normLimit : Tendsto (fun time => ‖quotient time - derivative‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simp_rw [← normSquare] at sumLimit
    have root := Real.continuous_sqrt.continuousAt.tendsto.comp sumLimit
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using root
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add, translate_zero] using (tendsto_iff_norm_sub_tendsto_zero.mpr normLimit)

theorem translate_hasDerivAt (direction : Fin 3) (state derivative : ScalarSequence)
    (generated : ∀ wave, derivative wave = multiplier wave direction * state wave) (time : ℝ) :
    HasDerivAt (fun actual => translate direction actual state) (translate direction time derivative) time := by
  have localDerivative := translate_hasDerivAt_zero direction (translate direction time state)
    (translate direction time derivative) (fun wave => by
      change phase direction time wave * derivative wave = multiplier wave direction *
        (phase direction time wave * state wave)
      rw [generated]
      ring)
  have shifted (increment : ℝ) : translate direction (time + increment) state =
      translate direction increment (translate direction time state) := by
    rw [add_comm, translate_add]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp_rw [shifted]
  simpa only [zero_add, translate_zero] using localDerivative.tendsto_slope_zero

end
end SaturationMonoid.NavierStokes.NativeSpatialTranslation
