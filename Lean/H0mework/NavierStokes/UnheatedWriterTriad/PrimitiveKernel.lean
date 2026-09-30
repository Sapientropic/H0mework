import H0mework.NavierStokes.UnheatedWriterTriad.Channels

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadPrimitiveKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeUnheatedTriadKernel NativeUnheatedStressPairEvolution NativeCompleteStressCarrier
noncomputable section
variable {nu : Viscosity}

theorem output_root_le (a b c : IntegerWavevector) :
    Real.sqrt (integerWaveViscousMultiplier (a+b)) ≤ (2 / (2*Real.pi)) *
      (integerWaveViscousMultiplier a + integerWaveViscousMultiplier b + integerWaveViscousMultiplier c) := by
  by_cases zero : a+b = 0
  · rw [zero]
    simp only [integerWaveViscousMultiplier, integerWaveNormSq, Pi.zero_apply, Int.cast_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero, Real.sqrt_zero]
    positivity [integerWaveNormSq_nonneg a, integerWaveNormSq_nonneg b, integerWaveNormSq_nonneg c]
  · have floor : (2*Real.pi)^2 ≤ integerWaveViscousMultiplier (a+b) := by
      simpa only [mul_one, integerWaveViscousMultiplier] using mul_le_mul_of_nonneg_left (one_le_integerWaveNormSq (a+b) zero) (sq_nonneg (2*Real.pi))
    have rootFloor := (Real.le_sqrt (by positivity : 0 ≤ 2*Real.pi) (multiplier_nonnegative (a+b))).mpr floor
    have paid := mul_le_mul_of_nonneg_right rootFloor (Real.sqrt_nonneg (integerWaveViscousMultiplier (a+b)))
    rw [← pow_two, Real.sq_sqrt (multiplier_nonnegative (a+b))] at paid
    have output := output_multiplier a b
    have lower := multiplier_nonnegative c
    have bound : Real.sqrt (integerWaveViscousMultiplier (a+b)) ≤
        (2 * (integerWaveViscousMultiplier a + integerWaveViscousMultiplier b + integerWaveViscousMultiplier c)) / (2*Real.pi) :=
      (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by nlinarith only [paid, output, lower])
    exact bound.trans_eq (by ring)

theorem normalized_root_bound (a b c : IntegerWavevector) :
    Real.sqrt (integerWaveViscousMultiplier (a+b)) * (triadDecay nu a b c)⁻¹ ≤
      2 / (nu.coeff * (2*Real.pi)) := by
  have numerator : Real.sqrt (integerWaveViscousMultiplier (a+b)) ≤
      (2 / (nu.coeff * (2*Real.pi))) * triadDecay nu a b c := by
    convert output_root_le a b c using 1
    unfold triadDecay
    field_simp [nu.coeff_pos.ne']
  by_cases zero : triadDecay nu a b c = 0
  · rw [zero, inv_zero, mul_zero]
    positivity [nu.coeff_pos]
  · have paid := mul_le_mul_of_nonneg_right numerator (inv_nonneg.mpr (triad_nonnegative (nu := nu) a b c))
    simpa only [mul_assoc, mul_inv_cancel₀ zero, mul_one] using paid

def kernel (nu : Viscosity) (i j output : Coordinate) (a b c : IntegerWavevector) : ℂ :=
  ((decay nu (a+b) c)⁻¹ * (triadDecay nu a b c)⁻¹) • NativeUnheatedTriadChannels.pressure (a+b) i j output

def cap (nu : Viscosity) : ℝ :=
  (2 / (nu.coeff * (2*Real.pi))) * (nu.coeff * (2*Real.pi)^2)⁻¹

theorem kernel_bound (nu : Viscosity) (i j output : Coordinate) (a b c : IntegerWavevector) :
    ‖kernel nu i j output a b c‖ ≤ cap nu * weight c := by
  have decay0 : 0 ≤ decay nu (a+b) c :=
    mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative (a+b)) (multiplier_nonnegative c))
  have factor0 := mul_nonneg (inv_nonneg.mpr decay0) (inv_nonneg.mpr (triad_nonnegative (nu := nu) a b c))
  rw [kernel, norm_smul, Real.norm_of_nonneg factor0]
  calc
    _ ≤ ((decay nu (a+b) c)⁻¹ * (triadDecay nu a b c)⁻¹) * Real.sqrt (integerWaveViscousMultiplier (a+b)) :=
      mul_le_mul_of_nonneg_left (NativeUnheatedTriadChannels.pressure_bound (a+b) i j output) factor0
    _ ≤ (2 / (nu.coeff*(2*Real.pi))) * (decay nu (a+b) c)⁻¹ := by
      have paid := mul_le_mul_of_nonneg_right (normalized_root_bound (nu := nu) a b c) (inv_nonneg.mpr decay0)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using paid
    _ ≤ _ := (mul_le_mul_of_nonneg_left (inverse_internal_bound (nu := nu) (a+b) c)
      (by positivity [nu.coeff_pos])).trans_eq (by unfold cap; ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadPrimitiveKernel
