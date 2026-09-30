import H0mework.Versions.X.NavierStokes.HigherTreeSextic.ShiftSchur
import H0mework.Versions.X.NavierStokes.HigherTreeSexticUniform.Tail

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformSchur
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeUnheatedSexticLatticePower NativeUnheatedSexticUniformPrefix NativeUnheatedSexticUniformTail
open NativeUnheatedSexticShiftSchur (kernel kernel_nonnegative kernel_symmetric)
noncomputable section

theorem low_point (wave first last : IntegerWavevector) :
    kernel wave first last*density 3 last ≤ ((radius first : ℝ)^2)⁻¹*
      (density 3 last*density 2 (wave-first-last)) := by
  have lower : (radius first : ℝ)^2 ≤ mass first+mass last :=
    (radius_lower first).trans (by linarith [mass_positive last])
  have paid := inv_anti₀ (sq_pos_of_pos (Nat.cast_pos.mpr (radius_positive first))) lower
  have product := mul_le_mul_of_nonneg_left paid
    (mul_nonneg (density_positive 2 (wave-first-last)).le (density_positive 3 last).le)
  unfold kernel
  convert! product using 1 <;> ring

theorem high_point (wave first last : IntegerWavevector) :
    kernel wave first last*density 3 last ≤ density 7 last*density 2 (wave-first-last) := by
  have paid := inv_anti₀ (mass_positive last) (show mass last ≤ mass first+mass last by linarith [mass_positive first])
  have product := mul_le_mul_of_nonneg_left paid
    (mul_nonneg (density_positive 2 (wave-first-last)).le (density_positive 3 last).le)
  rw [show 7=4+3 by omega, density_add, density_four]
  unfold kernel
  convert! product using 1 <;> ring

theorem low_sum (wave first : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ last ∈ observed ∩ integerWaveFrequencyCube (radius first), kernel wave first last*density 3 last) ≤
      4320*decay (radius first) := by
  have compared := Finset.sum_le_sum (s := observed ∩ integerWaveFrequencyCube (radius first))
    (fun last _ => low_point wave first last)
  rw [← Finset.mul_sum] at compared
  have included : (∑ last ∈ observed ∩ integerWaveFrequencyCube (radius first),
      density 3 last*density 2 (wave-first-last)) ≤ amount 3 (wave-first) (radius first) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun last _ _ => mul_nonneg (density_positive 3 last).le (density_positive 2 (wave-first-last)).le)
  have paid := compared.trans (mul_le_mul_of_nonneg_left
    (included.trans (weighted_prefix (wave-first) (radius first) (radius_positive first))) (by positivity))
  apply paid.trans_eq
  have root := Real.sq_sqrt (Nat.cast_nonneg (radius first))
  have rootPositive := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (radius_positive first))
  have positive : (0 : ℝ) < radius first := Nat.cast_pos.mpr (radius_positive first)
  unfold decay
  field_simp
  linear_combination root

theorem high_sum (wave first : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ last ∈ observed \ integerWaveFrequencyCube (radius first), kernel wave first last*density 3 last) ≤
      4320*decay (radius first) :=
  (Finset.sum_le_sum fun last _ => high_point wave first last).trans
    (weighted_tail (wave-first) (radius first) (radius_positive first) observed)

theorem row_bound (wave first : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ last ∈ observed, kernel wave first last*density 3 last) ≤ 34560*density 3 first := by
  have combined := add_le_add (low_sum wave first observed) (high_sum wave first observed)
  rw [Finset.sum_inter_add_sum_sdiff] at combined
  have paid := mul_le_mul_of_nonneg_left (radius_density first) (by norm_num : (0 : ℝ) ≤ 8640)
  unfold decay at combined
  nlinarith

theorem column_bound (wave last : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ first ∈ observed, kernel wave first last*density 3 first) ≤ 34560*density 3 last := by
  simpa only [kernel_symmetric wave] using row_bound wave last observed

theorem summable (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (NativeUnheatedSchur.term (kernel wave) left right) :=
  NativeUnheatedSchur.summable (kernel wave) (density 3) 34560 (kernel_nonnegative wave) (density_positive 3)
    (by norm_num) (row_bound wave) (column_bound wave) left right

theorem bound (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, NativeUnheatedSchur.term (kernel wave) left right index) ≤ 34560*‖left‖*‖right‖ :=
  NativeUnheatedSchur.bound (kernel wave) (density 3) 34560 (kernel_nonnegative wave) (density_positive 3)
    (by norm_num) (row_bound wave) (column_bound wave) left right

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformSchur
