import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.NormalForm
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Kernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticOutput
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedQuinticTime NativeUnheatedTriadKernel NativeCompleteStressCarrier
noncomputable section
variable {nu : Viscosity}

theorem output_multiplier (a b c d e : Slot) :
    integerWaveViscousMultiplier (a.1+b.1+c.1+d.1+e.1) ≤
      8*(integerWaveViscousMultiplier a.1+integerWaveViscousMultiplier b.1+
        integerWaveViscousMultiplier c.1+integerWaveViscousMultiplier d.1+integerWaveViscousMultiplier e.1) := by
  linarith [NativeUnheatedTriadKernel.output_multiplier (a.1+b.1+c.1+d.1) e.1,
    NativeUnheatedQuarticKernel.output_multiplier a b c d, multiplier_nonnegative e.1]

theorem decay_coercivity (a b c d e : Slot) :
    nu.coeff*integerWaveViscousMultiplier (a.1+b.1+c.1+d.1+e.1) ≤ 8*sumRate nu a b c d e :=
  (mul_le_mul_of_nonneg_left (output_multiplier a b c d e) nu.coeff_pos.le).trans_eq (by unfold sumRate; ring)

def scale (nu : Viscosity) : ℝ := nu.coeff*(2*Real.pi)^2/8

theorem scale_positive (nu : Viscosity) : 0 < scale nu := by
  unfold scale
  positivity [nu.coeff_pos]

theorem rate_floor (a b c d e : Slot) (nonzero : a.1 ≠ 0 ∨ b.1 ≠ 0 ∨ c.1 ≠ 0 ∨ d.1 ≠ 0 ∨ e.1 ≠ 0) :
    nu.coeff*(2*Real.pi)^2 ≤ sumRate nu a b c d e := by
  have lower : 1 ≤ integerWaveNormSq a.1+integerWaveNormSq b.1+integerWaveNormSq c.1+integerWaveNormSq d.1+integerWaveNormSq e.1 := by
    rcases nonzero with first | second | third | fourth | last
    all_goals linarith [one_le_integerWaveNormSq _ (by assumption), integerWaveNormSq_nonneg a.1,
      integerWaveNormSq_nonneg b.1, integerWaveNormSq_nonneg c.1, integerWaveNormSq_nonneg d.1, integerWaveNormSq_nonneg e.1]
  have paid := mul_le_mul_of_nonneg_left lower (mul_nonneg nu.coeff_pos.le (sq_nonneg (2*Real.pi)))
  simpa only [mul_one, sumRate, integerWaveViscousMultiplier, mul_add, mul_assoc] using paid

theorem inverse_bound (a b c d e : Slot) :
    (sumRate nu a b c d e)⁻¹ ≤ (scale nu)⁻¹*weight (a.1+b.1+c.1+d.1+e.1) := by
  by_cases nonzero : a.1 ≠ 0 ∨ b.1 ≠ 0 ∨ c.1 ≠ 0 ∨ d.1 ≠ 0 ∨ e.1 ≠ 0
  · have lower : scale nu*(weight (a.1+b.1+c.1+d.1+e.1))⁻¹ ≤ sumRate nu a b c d e := by
      by_cases zero : a.1+b.1+c.1+d.1+e.1 = 0
      · simp only [weight, if_pos zero, inv_one, mul_one]
        have paid := rate_floor (nu := nu) a b c d e nonzero
        have positive := scale_positive nu
        unfold scale at positive ⊢
        linarith
      · simp only [weight, if_neg zero, inv_inv]
        have paid := decay_coercivity (nu := nu) a b c d e
        unfold integerWaveViscousMultiplier at paid
        unfold scale
        nlinarith
    have positive : 0 < scale nu*(weight (a.1+b.1+c.1+d.1+e.1))⁻¹ :=
      mul_pos (scale_positive nu) (inv_pos.mpr (weight_pos _))
    simpa only [one_div, mul_inv_rev, inv_inv, mul_comm] using one_div_le_one_div_of_le positive lower
  · push Not at nonzero
    obtain ⟨first,second,third,fourth,last⟩ := nonzero
    have zero : sumRate nu a b c d e = 0 := by
      simp [sumRate, first, second, third, fourth, last, integerWaveViscousMultiplier, integerWaveNormSq]
    rw [zero, inv_zero]
    exact mul_nonneg (inv_nonneg.mpr (scale_positive nu).le) (weight_pos _).le

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ) (time : ℝ) :
    NativeUnheatedQuinticNormalForm.primitive seed a b c d e kernel time =
      (sumRate nu a b c d e)⁻¹ • (kernel*product seed a b c d e time) := by
  simp only [NativeUnheatedQuinticNormalForm.primitive, NativeUnheatedQuinticNormalForm.normalizer, smul_mul_assoc]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticOutput
