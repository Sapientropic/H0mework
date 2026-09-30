import H0mework.NavierStokes.UnheatedWriterQuartic.Time
import H0mework.NavierStokes.UnheatedWriterTriad.Output

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedQuarticTime NativeUnheatedTriadKernel NativeEndpointVelocityCarrier
noncomputable section
variable {nu : Viscosity}

theorem rate_nonnegative (a b c d : Slot) : 0 ≤ sumRate nu a b c d :=
  mul_nonneg nu.coeff_pos.le (add_nonneg (add_nonneg (add_nonneg
    (multiplier_nonnegative a.1) (multiplier_nonnegative b.1)) (multiplier_nonnegative c.1)) (multiplier_nonnegative d.1))

theorem output_multiplier (a b c d : Slot) :
    integerWaveViscousMultiplier (a.1+b.1+c.1+d.1) ≤
      4*(integerWaveViscousMultiplier a.1+integerWaveViscousMultiplier b.1+
        integerWaveViscousMultiplier c.1+integerWaveViscousMultiplier d.1) := by
  have paired := NativeUnheatedTriadKernel.output_multiplier (a.1+b.1) (c.1+d.1)
  rw [← add_assoc] at paired
  linarith [NativeUnheatedTriadKernel.output_multiplier a.1 b.1,
    NativeUnheatedTriadKernel.output_multiplier c.1 d.1]

theorem decay_coercivity (a b c d : Slot) :
    nu.coeff*integerWaveViscousMultiplier (a.1+b.1+c.1+d.1) ≤ 4*sumRate nu a b c d := by
  exact (mul_le_mul_of_nonneg_left (output_multiplier a b c d) nu.coeff_pos.le).trans_eq (by unfold sumRate; ring)

theorem parent_triad_bound (a b c d : Slot) :
    triadDecay nu (a.1+b.1) c.1 d.1 ≤ 2*sumRate nu a b c d := by
  have original := NativeUnheatedTriadKernel.output_multiplier a.1 b.1
  have positive := mul_le_mul_of_nonneg_left original nu.coeff_pos.le
  unfold triadDecay sumRate
  nlinarith [multiplier_nonnegative c.1, multiplier_nonnegative d.1, nu.coeff_pos]

theorem parent_pair_bound (a b c d : Slot) :
    NativeUnheatedStressPairEvolution.decay nu (a.1+b.1+c.1) d.1 ≤ 3*sumRate nu a b c d := by
  have original := NativeUnheatedTriadOutput.output_multiplier a.1 b.1 c.1
  have positive := mul_le_mul_of_nonneg_left original nu.coeff_pos.le
  unfold NativeUnheatedStressPairEvolution.decay sumRate
  nlinarith [multiplier_nonnegative d.1, nu.coeff_pos]

theorem extract (a b c d : Slot) :
    integerWaveViscousMultiplier (a.1+b.1+c.1+d.1)*(sumRate nu a b c d)⁻¹ ≤ 4/nu.coeff := by
  have dominated : integerWaveViscousMultiplier (a.1+b.1+c.1+d.1) ≤ (4/nu.coeff)*sumRate nu a b c d := by
    have same : (4/nu.coeff)*sumRate nu a b c d = 4*(integerWaveViscousMultiplier a.1+
        integerWaveViscousMultiplier b.1+integerWaveViscousMultiplier c.1+integerWaveViscousMultiplier d.1) := by
      unfold sumRate
      field_simp [nu.coeff_pos.ne']
    rw [same]
    exact output_multiplier a b c d
  by_cases zero : sumRate nu a b c d = 0
  · simp only [zero, inv_zero, mul_zero]
    positivity [nu.coeff_pos]
  · exact (mul_le_mul_of_nonneg_right dominated (inv_nonneg.mpr (rate_nonnegative a b c d))).trans_eq
      (by rw [mul_assoc, mul_inv_cancel₀ zero, mul_one])

theorem rate_zero_first (a b c d : Slot) (zero : sumRate nu a b c d = 0) : a.1 = 0 := by
  by_contra nonzero
  have positive : 0 < integerWaveViscousMultiplier a.1 :=
    mul_pos (by positivity) (integerWaveNormSq_pos nonzero)
  unfold sumRate at zero
  nlinarith [nu.coeff_pos, multiplier_nonnegative b.1, multiplier_nonnegative c.1, multiplier_nonnegative d.1]

theorem product_zero_rate (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot)
    (zero : sumRate nu a b c d = 0) (time : ℝ) : product seed a b c d time = 0 := by
  have first := rate_zero_first a b c d zero
  simp only [product, NativeUnheatedTriadRows.velocity, NativeUnheatedTriadRows.decode_apply,
    first, wholeVelocity_zero, Pi.zero_apply, smul_zero, zero_mul]

theorem forcing_zero_rate (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot)
    (zero : sumRate nu a b c d = 0) (time : ℝ) : forcing seed a b c d time = 0 := by
  have first := rate_zero_first a b c d zero
  simp only [forcing, NativeUnheatedTriadRows.velocity, NativeUnheatedTriadRows.action, NativeUnheatedTriadRows.decode_apply,
    first, wholeVelocity_zero, Pi.zero_apply, smul_zero, zero_mul, add_zero]

def normalizer (nu : Viscosity) (a b c d : Slot) (kernel : ℂ) : ℂ :=
  ((sumRate nu a b c d)⁻¹ : ℝ) • kernel

theorem normalizer_product (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot)
    (kernel : ℂ) (time : ℝ) :
    normalizer nu a b c d kernel*(sumRate nu a b c d • product seed a b c d time) =
      kernel*product seed a b c d time := by
  by_cases zero : sumRate nu a b c d = 0
  · rw [product_zero_rate seed a b c d zero time, smul_zero, mul_zero, mul_zero]
  · simp only [normalizer, Complex.real_smul, ← mul_assoc, mul_right_comm _ kernel,
      ← Complex.ofReal_mul, inv_mul_cancel₀ zero, Complex.ofReal_one, one_mul]
    exact mul_comm _ _

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticKernel
