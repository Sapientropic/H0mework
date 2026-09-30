import H0mework.Versions.X.NavierStokes.HigherTreeSextic.ShiftSchur
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.Hardy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticQuarterSchur
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedSexticLatticePower
noncomputable section

def kernel (wave first last : IntegerWavevector) : ℝ :=
  density 1 (wave-first-last)/((mass first+mass last)*Real.sqrt (Real.sqrt (mass first+mass last)))

theorem kernel_nonnegative (wave first last : IntegerWavevector) : 0 ≤ kernel wave first last := by
  unfold kernel
  positivity [density_positive 1 (wave-first-last), mass_positive first, mass_positive last]

theorem kernel_symmetric (wave first last : IntegerWavevector) : kernel wave first last = kernel wave last first := by
  have same : wave-first-last = wave-last-first := by abel
  simp only [kernel, same, add_comm]

theorem kernel_rpow (wave first last : IntegerWavevector) :
    kernel wave first last = mass (wave-first-last)^(-1/4 : ℝ)*(mass first+mass last)^(-5/4 : ℝ) := by
  have positive := add_pos (mass_positive first) (mass_positive last)
  have root : Real.sqrt (Real.sqrt (mass first+mass last)) = (mass first+mass last)^(1/4 : ℝ) := by
    simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul positive.le]
    norm_num
  have denominator : (mass first+mass last)*Real.sqrt (Real.sqrt (mass first+mass last)) =
      (mass first+mass last)^(5/4 : ℝ) := by
    calc
      _ = (mass first+mass last)^(1 : ℝ)*(mass first+mass last)^(1/4 : ℝ) := by rw [Real.rpow_one, root]
      _ = (mass first+mass last)^((1 : ℝ)+1/4) := (Real.rpow_add positive _ _).symm
      _ = _ := by congr 1; norm_num
  rw [kernel, density_rpow, denominator, div_eq_mul_inv, ← Real.rpow_neg positive.le]
  norm_num

def base (first last : IntegerWavevector) : ℝ :=
  ((mass first+mass last)*Real.sqrt (mass first+mass last))⁻¹

theorem base_nonnegative (first last : IntegerWavevector) : 0 ≤ base first last := by
  unfold base
  positivity [mass_positive first, mass_positive last]

theorem kernel_square (wave first last : IntegerWavevector) :
    kernel wave first last^2 = NativeUnheatedSexticShiftSchur.kernel wave first last*base first last := by
  have numerator : density 1 (wave-first-last)^2 = density 2 (wave-first-last) := by
    rw [pow_two, ← density_add]
  rw [kernel, div_pow, mul_pow, numerator, Real.sq_sqrt (Real.sqrt_nonneg _)]
  unfold NativeUnheatedSexticShiftSchur.kernel base
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

theorem base_bound (first last : IntegerWavevector) : base first last ≤ NativeUnheatedSexticHardy.kernel first last := by
  have positive := add_pos (mass_positive first) (mass_positive last)
  have root := Real.sqrt_le_sqrt (show mass last ≤ mass first+mass last by linarith [mass_positive first])
  have inverse := inv_anti₀ (Real.sqrt_pos.mpr (mass_positive last)) root
  calc
    _ = (Real.sqrt (mass first+mass last))⁻¹/(mass first+mass last) := by simp only [base, div_eq_mul_inv, mul_inv_rev]
    _ ≤ (Real.sqrt (mass last))⁻¹/(mass first+mass last) := div_le_div_of_nonneg_right inverse positive.le
    _ = _ := by rw [NativeUnheatedSexticHardy.kernel, density, radical_square]

theorem point_bound (wave first last : IntegerWavevector) :
    2*kernel wave first last ≤ NativeUnheatedSexticShiftSchur.kernel wave first last+NativeUnheatedSexticHardy.kernel first last := by
  have arithmetic := two_mul_le_add_of_sq_le_mul (NativeUnheatedSexticShiftSchur.kernel_nonnegative wave first last)
    (base_nonnegative first last) (kernel_square wave first last).le
  exact arithmetic.trans (add_le_add le_rfl (base_bound first last))

theorem radical_one (wave : IntegerWavevector) : 1 ≤ radical wave := by
  simpa only [Nat.cast_one, Real.sqrt_one] using radical_lower 1 wave (by simpa using mass_one wave)

def cap (wave : IntegerWavevector) : ℝ := 400512*radical wave

theorem cap_nonnegative (wave : IntegerWavevector) : 0 ≤ cap wave := mul_nonneg (by norm_num) (radical_positive wave).le

theorem cap_payment (wave : IntegerWavevector) : (NativeUnheatedSexticShiftSchur.cap wave+512)/2 ≤ cap wave := by
  unfold cap NativeUnheatedSexticShiftSchur.cap
  linarith [radical_one wave]

theorem row_bound (wave first : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ last ∈ F, kernel wave first last*density 3 last) ≤ cap wave*density 3 first := by
  have point (last : IntegerWavevector) : 2*(kernel wave first last*density 3 last) ≤
      NativeUnheatedSexticShiftSchur.kernel wave first last*density 3 last+
        NativeUnheatedSexticHardy.kernel first last*density 3 last := by
    have paid := mul_le_mul_of_nonneg_right (point_bound wave first last) (density_positive 3 last).le
    nlinarith only [paid]
  have compared := Finset.sum_le_sum (s := F) (fun last _ => point last)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at compared
  have paid := add_le_add (NativeUnheatedSexticShiftSchur.row_bound wave first F)
    (NativeUnheatedSexticHardy.row_bound first F)
  have firstBound : (∑ last ∈ F, kernel wave first last*density 3 last) ≤
      ((NativeUnheatedSexticShiftSchur.cap wave+512)/2)*density 3 first := by linarith
  exact firstBound.trans (mul_le_mul_of_nonneg_right (cap_payment wave) (density_positive 3 first).le)

theorem column_bound (wave last : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ first ∈ F, kernel wave first last*density 3 first) ≤ cap wave*density 3 last := by
  simpa only [kernel_symmetric wave] using row_bound wave last F

theorem summable (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (NativeUnheatedSchur.term (kernel wave) left right) :=
  NativeUnheatedSchur.summable (kernel wave) (density 3) (cap wave) (kernel_nonnegative wave)
    (density_positive 3) (cap_nonnegative wave) (row_bound wave) (column_bound wave) left right

theorem bound (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, NativeUnheatedSchur.term (kernel wave) left right index) ≤ cap wave*‖left‖*‖right‖ :=
  NativeUnheatedSchur.bound (kernel wave) (density 3) (cap wave) (kernel_nonnegative wave)
    (density_positive 3) (cap_nonnegative wave) (row_bound wave) (column_bound wave) left right

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticQuarterSchur
