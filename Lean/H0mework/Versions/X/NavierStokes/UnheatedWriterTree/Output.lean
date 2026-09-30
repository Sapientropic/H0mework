import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Time
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Kernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeOutput
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeUnheatedTreeTime NativeUnheatedTriadKernel NativeCompleteStressCarrier
noncomputable section
variable {nu : Viscosity} {n : ℕ}

def output (slots : Fin (n+1) → Slot) : IntegerWavevector := ∑ number : Fin (n+1), (slots number).1

theorem rate_nonnegative (slots : Fin (n+1) → Slot) : 0 ≤ sumRate nu slots :=
  mul_nonneg nu.coeff_pos.le (Finset.sum_nonneg fun number _ => multiplier_nonnegative (slots number).1)

theorem rate_zero_wave (slots : Fin (n+1) → Slot) (zero : sumRate nu slots = 0) (number : Fin (n+1)) :
    (slots number).1 = 0 := by
  have lower := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (n+1))))
    (fun other _ => multiplier_nonnegative (slots other).1) (Finset.mem_univ number)
  have paid := mul_le_mul_of_nonneg_left lower nu.coeff_pos.le
  change nu.coeff*integerWaveViscousMultiplier (slots number).1 ≤ sumRate nu slots at paid
  rw [zero] at paid
  by_contra nonzero
  have positive : 0 < integerWaveViscousMultiplier (slots number).1 :=
    mul_pos (by positivity) (integerWaveNormSq_pos nonzero)
  exact (not_le_of_gt (mul_pos nu.coeff_pos positive)) paid

theorem output_multiplier (slots : Fin (n+1) → Slot) :
    integerWaveViscousMultiplier (output slots) ≤
      (n+1 : ℝ)*(∑ number : Fin (n+1), integerWaveViscousMultiplier (slots number).1) := by
  have row (coordinate : Coordinate) :
      (∑ number : Fin (n+1), ((slots number).1 coordinate : ℝ))^2 ≤
        (n+1 : ℝ)*(∑ number : Fin (n+1), ((slots number).1 coordinate : ℝ)^2) := by
    have cauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (n+1)))
      (fun _ => (1 : ℝ)) (fun number => ((slots number).1 coordinate : ℝ))
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one] using cauchy
  have summed := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun coordinate _ => row coordinate)
  rw [← Finset.mul_sum, Finset.sum_comm] at summed
  have paid := mul_le_mul_of_nonneg_left summed (sq_nonneg (2*Real.pi))
  convert! paid using 1
  · simp only [output, integerWaveViscousMultiplier, integerWaveNormSq, Finset.sum_apply, Int.cast_sum]
  · simp only [integerWaveViscousMultiplier, integerWaveNormSq, ← Finset.mul_sum]
    ring

theorem decay_coercivity (slots : Fin (n+1) → Slot) :
    nu.coeff*integerWaveViscousMultiplier (output slots) ≤ (n+1 : ℝ)*sumRate nu slots :=
  (mul_le_mul_of_nonneg_left (output_multiplier slots) nu.coeff_pos.le).trans_eq (by unfold sumRate; ring)

def scale (nu : Viscosity) (n : ℕ) : ℝ := nu.coeff*(2*Real.pi)^2/(n+1 : ℝ)

theorem scale_positive (nu : Viscosity) (n : ℕ) : 0 < scale nu n := by
  unfold scale
  positivity [nu.coeff_pos]

theorem scale_le_floor (nu : Viscosity) (n : ℕ) : scale nu n ≤ nu.coeff*(2*Real.pi)^2 := by
  unfold scale
  have below := div_le_div_of_nonneg_left (mul_nonneg nu.coeff_pos.le (sq_nonneg (2*Real.pi)))
    (by norm_num : (0 : ℝ) < 1) (show (1 : ℝ) ≤ n+1 by linarith [Nat.cast_nonneg (α := ℝ) n])
  simpa only [div_one] using below

theorem rate_floor (slots : Fin (n+1) → Slot) (nonzero : ∃ number, (slots number).1 ≠ 0) :
    nu.coeff*(2*Real.pi)^2 ≤ sumRate nu slots := by
  obtain ⟨number, nonzero⟩ := nonzero
  have waveBound : (2*Real.pi)^2 ≤ integerWaveViscousMultiplier (slots number).1 := by
    simpa only [mul_one, integerWaveViscousMultiplier] using
      mul_le_mul_of_nonneg_left (one_le_integerWaveNormSq _ nonzero) (sq_nonneg (2*Real.pi))
  have sumBound := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (n+1))))
    (fun other _ => multiplier_nonnegative (slots other).1) (Finset.mem_univ number)
  exact mul_le_mul_of_nonneg_left (waveBound.trans sumBound) nu.coeff_pos.le

theorem inverse_bound (slots : Fin (n+1) → Slot) :
    (sumRate nu slots)⁻¹ ≤ (scale nu n)⁻¹*weight (output slots) := by
  by_cases nonzero : ∃ number, (slots number).1 ≠ 0
  · have lower : scale nu n*(weight (output slots))⁻¹ ≤ sumRate nu slots := by
      by_cases zero : output slots = 0
      · simp only [weight, if_pos zero, inv_one, mul_one]
        exact (scale_le_floor nu n).trans (rate_floor slots nonzero)
      · simp only [weight, if_neg zero, inv_inv, scale, div_mul_eq_mul_div]
        apply (div_le_iff₀ (show (0 : ℝ) < n+1 by positivity)).mpr
        have paid := decay_coercivity (nu := nu) slots
        simpa only [integerWaveViscousMultiplier, mul_assoc, mul_comm (sumRate nu slots)] using paid
    have positive : 0 < scale nu n*(weight (output slots))⁻¹ :=
      mul_pos (scale_positive nu n) (inv_pos.mpr (weight_pos _))
    simpa only [one_div, mul_inv_rev, inv_inv, mul_comm] using one_div_le_one_div_of_le positive lower
  · push Not at nonzero
    have zero : sumRate nu slots = 0 := by
      simp only [sumRate, nonzero, integerWaveViscousMultiplier, integerWaveNormSq, Pi.zero_apply,
        Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero]
    rw [zero, inv_zero]
    exact mul_nonneg (inv_nonneg.mpr (scale_positive nu n).le) (weight_pos _).le

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeOutput
