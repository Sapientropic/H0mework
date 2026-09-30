import H0mework.Versions.X.NavierStokes.HigherTreeSextic.ShiftRiesz
import H0mework.NavierStokes.HigherTreeSextic.Schur

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticShiftSchur
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativeUnheatedSexticLatticePower
noncomputable section

def kernel (wave first last : IntegerWavevector) : ℝ := density 2 (wave-first-last)/(mass first+mass last)

theorem kernel_nonnegative (wave first last : IntegerWavevector) : 0 ≤ kernel wave first last :=
  div_nonneg (density_positive 2 _).le (add_pos (mass_positive _) (mass_positive _)).le

theorem kernel_symmetric (wave first last : IntegerWavevector) : kernel wave first last = kernel wave last first := by
  have same : wave-first-last = wave-last-first := by abel
  simp only [kernel, same, add_comm]

theorem inverse_pair (first last : IntegerWavevector) :
    (mass first+mass last)⁻¹ ≤ density 2 first*density 2 last := by
  have lower : radical first^2*radical last^2 ≤ mass first+mass last := by
    rw [← radical_fourth first, ← radical_fourth last]
    nlinarith [sq_nonneg (radical first^2-radical last^2), sq_nonneg (radical first^2), sq_nonneg (radical last^2)]
  have paid := inv_anti₀ (mul_pos (pow_pos (radical_positive first) 2) (pow_pos (radical_positive last) 2)) lower
  simpa only [density, mul_inv_rev, mul_comm] using paid

theorem point_bound (wave first last : IntegerWavevector) :
    kernel wave first last*density 3 last ≤ density 2 first*(density 5 last*density 2 (wave-first-last)) := by
  have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (inverse_pair first last)
    (density_positive 2 (wave-first-last)).le) (density_positive 3 last).le
  rw [show (5 : ℕ)=2+3 by norm_num, density_add]
  unfold kernel
  convert! paid using 1
  ring

theorem translate_weight (wave first : IntegerWavevector) :
    density 2 first*density 1 (wave-first) ≤ 2*radical wave*density 3 first := by
  have triangle := NativeUnheatedSexticShiftRiesz.mass_triangle wave (first-wave)
  have reverse : mass (first-wave) = mass (wave-first) := by
    unfold mass integerWaveNormSq
    congr 1
    apply Finset.sum_congr rfl
    intro coordinate _
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [add_sub_cancel, reverse] at triangle
  have product : mass first ≤ 4*mass wave*mass (wave-first) := by
    nlinarith [mass_one wave, mass_one (wave-first), mul_nonneg (sub_nonneg.mpr (mass_one wave)) (sub_nonneg.mpr (mass_one (wave-first)))]
  have radicalBound : radical first ≤ 2*radical wave*radical (wave-first) := by
    apply (pow_le_pow_iff_left₀ (radical_positive first).le (by positivity [radical_positive wave, radical_positive (wave-first)]) (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [mul_pow, mul_pow, radical_fourth, radical_fourth, radical_fourth]
    nlinarith [mul_pos (mass_positive wave) (mass_positive (wave-first))]
  have paid := mul_le_mul_of_nonneg_right radicalBound
    (inv_nonneg.mpr (mul_nonneg (pow_nonneg (radical_positive first).le 3) (radical_positive (wave-first)).le))
  convert! paid using 1 <;> dsimp only [density] <;>
    field_simp [(radical_positive first).ne', (radical_positive (wave-first)).ne']

def cap (wave : IntegerWavevector) : ℝ := 400000*radical wave

theorem cap_nonnegative (wave : IntegerWavevector) : 0 ≤ cap wave := mul_nonneg (by norm_num) (radical_positive wave).le

theorem row_bound (wave first : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ last ∈ observed, kernel wave first last*density 3 last) ≤ cap wave*density 3 first := by
  have compared := Finset.sum_le_sum (s := observed) fun last _ => point_bound wave first last
  rw [← Finset.mul_sum] at compared
  have paid := mul_le_mul_of_nonneg_left (NativeUnheatedSexticShiftRiesz.finite_bound (wave-first) observed) (density_positive 2 first).le
  apply (compared.trans paid).trans
  have same := mul_le_mul_of_nonneg_left (translate_weight wave first) (by norm_num : (0 : ℝ) ≤ 200000)
  change _ ≤ 400000*radical wave*density 3 first
  convert! same using 1 <;> ring

theorem column_bound (wave last : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ first ∈ observed, kernel wave first last*density 3 first) ≤ cap wave*density 3 last := by
  simpa only [kernel_symmetric wave] using row_bound wave last observed

theorem summable (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (NativeUnheatedSchur.term (kernel wave) left right) :=
  NativeUnheatedSchur.summable (kernel wave) (density 3) (cap wave) (kernel_nonnegative wave) (density_positive 3)
    (cap_nonnegative wave) (row_bound wave) (column_bound wave) left right

theorem bound (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, NativeUnheatedSchur.term (kernel wave) left right index) ≤ cap wave*‖left‖*‖right‖ :=
  NativeUnheatedSchur.bound (kernel wave) (density 3) (cap wave) (kernel_nonnegative wave) (density_positive 3)
    (cap_nonnegative wave) (row_bound wave) (column_bound wave) left right

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticShiftSchur
