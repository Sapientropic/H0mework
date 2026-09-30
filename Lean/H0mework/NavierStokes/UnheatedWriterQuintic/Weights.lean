import H0mework.NavierStokes.UnheatedWriterQuartic.AllSlots
import H0mework.NavierStokes.UnheatedWriterHalf.Source
import H0mework.NavierStokes.UnheatedWriterTriad.DepthKernel
import H0mework.NavierStokes.StressMovingSource.ProductWeights

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticWeights
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeCompleteStressCarrier NativeUnheatedTriadKernel NativeUnheatedTriadDepthKernel
noncomputable section
variable {nu : Viscosity}

def eta (wave : IntegerWavevector) : ℝ := weight wave ^ (7/8 : ℝ)
theorem eta_nonnegative (wave : IntegerWavevector) : 0 ≤ eta wave := Real.rpow_nonneg (weight_pos wave).le _

theorem eta_eighth (wave : IntegerWavevector) : eta wave ^ 8 = weight wave ^ 7 := by
  rw [eta, ← Real.rpow_mul_natCast (weight_pos wave).le]
  norm_num

theorem eta_square_summable : Summable (fun wave => eta wave^2) := by
  have paid := (hasSum_ite_eq (0 : IntegerWavevector) (1 : ℝ)).summable.add NativeMovingCriticalProductWeights.kernel_summable
  apply paid.congr
  intro wave
  by_cases zero : wave = 0
  · subst wave
    simp [eta, weight, NativeMovingCriticalProductWeights.weight, integerWaveNormSq]
  · simp only [eta, weight, if_neg zero, zero_add, NativeMovingCriticalProductWeights.weight]
    rw [Real.inv_rpow (integerWaveNormSq_nonneg wave)]

theorem paid_inverse {x y z : ℝ} (y0 : 0 ≤ y) (z0 : 0 ≤ z) (paid : x ≤ z*y) : x*y⁻¹ ≤ z := by
  by_cases zero : y = 0
  · simp only [zero, inv_zero, mul_zero]
    exact z0
  · exact (mul_le_mul_of_nonneg_right paid (inv_nonneg.mpr y0)).trans_eq (by rw [mul_assoc, mul_inv_cancel₀ zero, mul_one])

theorem triad_inverse_internal (a b c : IntegerWavevector) (index : Fin 3) :
    (triadDecay nu a b c)⁻¹ ≤ (floor nu)⁻¹*weight (![a,b,c] index) := by
  by_cases zero : ![a,b,c] index = 0
  · rw [weight, if_pos zero, mul_one]
    exact inverse_uniform a b c
  · have positive : 0 < nu.coeff*integerWaveViscousMultiplier (![a,b,c] index) :=
      mul_pos nu.coeff_pos (mul_pos (by positivity) (integerWaveNormSq_pos zero))
    have lower : nu.coeff*integerWaveViscousMultiplier (![a,b,c] index) ≤ triadDecay nu a b c := by
      fin_cases index
      · change nu.coeff*integerWaveViscousMultiplier a ≤ _
        unfold triadDecay
        nlinarith [nu.coeff_pos, multiplier_nonnegative b, multiplier_nonnegative c]
      · change nu.coeff*integerWaveViscousMultiplier b ≤ _
        unfold triadDecay
        nlinarith [nu.coeff_pos, multiplier_nonnegative a, multiplier_nonnegative c]
      · change nu.coeff*integerWaveViscousMultiplier c ≤ _
        unfold triadDecay
        nlinarith [nu.coeff_pos, multiplier_nonnegative a, multiplier_nonnegative b]
    have paid := one_div_le_one_div_of_le positive lower
    simpa only [one_div, weight, if_neg zero, floor, integerWaveViscousMultiplier, mul_inv_rev, mul_comm, mul_assoc] using paid

def powerCap (nu : Viscosity) : ℝ := 64*(nu.coeff⁻¹)^10*((floor nu)⁻¹)^14

theorem powerCap_nonnegative (nu : Viscosity) : 0 ≤ powerCap nu := by unfold powerCap; positivity

def cap (nu : Viscosity) : ℝ := powerCap nu ^ ((8 : ℝ)⁻¹)
theorem cap_nonnegative (nu : Viscosity) : 0 ≤ cap nu := Real.rpow_nonneg (powerCap_nonnegative nu) _
theorem cap_eighth (nu : Viscosity) : cap nu^8 = powerCap nu :=
  Real.rpow_inv_natCast_pow (powerCap_nonnegative nu) (by decide : (8 : ℕ) ≠ 0)

theorem from_eighth (nu : Viscosity) (value : ℂ) (first last : IntegerWavevector)
    (paid : ‖value‖^8 ≤ powerCap nu*weight first^7*weight last^7) :
    ‖value‖ ≤ cap nu*eta first*eta last := by
  apply le_of_pow_le_pow_left₀ (by decide : (8 : ℕ) ≠ 0) (by positivity [cap_nonnegative nu, eta_nonnegative first, eta_nonnegative last])
  simpa only [mul_pow, cap_eighth, eta_eighth] using paid

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticWeights
