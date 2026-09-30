import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticePrefix
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticeTail
import H0mework.NavierStokes.HigherTreeSextic.Schur

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticHardy
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeUnheatedSexticLatticePower NativeUnheatedSexticLatticePrefix NativeUnheatedSexticLatticeTail
noncomputable section

def kernel (first last : IntegerWavevector) : ℝ := density 2 last/(mass first+mass last)

theorem kernel_nonnegative (first last : IntegerWavevector) : 0 ≤ kernel first last :=
  div_nonneg (density_positive 2 last).le (add_nonneg (mass_positive first).le (mass_positive last).le)

theorem kernel_weight (first last : IntegerWavevector) :
    kernel first last*density 3 last = density 5 last/(mass first+mass last) := by
  rw [kernel, div_mul_eq_mul_div, ← density_add]

theorem density_two_radius (wave : IntegerWavevector) : density 2 wave ≤ (radius wave : ℝ)⁻¹ := by
  rw [density, radical_square]
  exact inv_anti₀ (Nat.cast_pos.mpr (radius_positive wave))
    ((Real.le_sqrt (Nat.cast_nonneg _) (mass_positive wave).le).mpr (radius_lower wave))

theorem root_div_square (value : ℝ) (positive : 0 < value) :
    Real.sqrt value/value^2 = (value*Real.sqrt value)⁻¹ := by
  have root := (Real.sqrt_pos.mpr positive).ne'
  calc
    _ = (Real.sqrt value)^2/(value^2*Real.sqrt value) := by field_simp [positive.ne', root]
    _ = _ := by rw [Real.sq_sqrt positive.le]; field_simp [positive.ne', root]

theorem row_low (wave : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ index ∈ F ∩ integerWaveFrequencyCube (radius wave), kernel wave index*density 3 index) ≤
      53*((radius wave : ℝ)*Real.sqrt (radius wave))⁻¹ := by
  have point (index : IntegerWavevector) : kernel wave index*density 3 index ≤
      density 5 index/(radius wave : ℝ)^2 := by
    rw [kernel_weight]
    exact div_le_div_of_nonneg_left (density_positive 5 index).le
      (sq_pos_of_pos (Nat.cast_pos.mpr (radius_positive wave)))
      ((radius_lower wave).trans (le_add_of_nonneg_right (mass_positive index).le))
  have compared := Finset.sum_le_sum (s := F ∩ integerWaveFrequencyCube (radius wave)) (fun index _ => point index)
  rw [← Finset.sum_div] at compared
  have paid := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right (s₁ := F))
    (fun index _ _ => (density_positive 5 index).le)).trans (prefix_five (radius wave) (radius_positive wave))
  apply compared.trans ((div_le_div_of_nonneg_right paid (sq_nonneg _)).trans_eq _)
  rw [mul_div_assoc, root_div_square _ (Nat.cast_pos.mpr (radius_positive wave))]

theorem row_high_point (first last : IntegerWavevector) : kernel first last*density 3 last ≤ density 9 last := by
  rw [kernel_weight]
  apply (div_le_div_of_nonneg_left (density_positive 5 last).le (mass_positive last)
    (le_add_of_nonneg_left (mass_positive first).le)).trans_eq
  rw [div_eq_mul_inv, ← density_four, ← density_add]

theorem row_bound (wave : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ index ∈ F, kernel wave index*density 3 index) ≤ 512*density 3 wave := by
  have high := (Finset.sum_le_sum (s := F \ integerWaveFrequencyCube (radius wave))
    (fun index _ => row_high_point wave index)).trans (nine_tail (radius wave) (radius_positive wave) F)
  rw [← Finset.sum_inter_add_sum_sdiff F (integerWaveFrequencyCube (radius wave))]
  apply (add_le_add (row_low wave F) high).trans
  have paid := mul_le_mul_of_nonneg_left (radius_density wave) (by norm_num : (0 : ℝ) ≤ 79)
  rw [div_eq_mul_inv]
  nlinarith [density_positive 3 wave]

theorem column_kernel (first last : IntegerWavevector) : kernel first last ≤ ((radius last : ℝ)^3)⁻¹ := by
  unfold kernel
  have denominator : (radius last : ℝ)^2 ≤ mass first+mass last :=
    (radius_lower last).trans (le_add_of_nonneg_left (mass_positive first).le)
  have paid := mul_le_mul (density_two_radius last)
    (inv_anti₀ (sq_pos_of_pos (Nat.cast_pos.mpr (radius_positive last))) denominator)
    (inv_nonneg.mpr (add_nonneg (mass_positive first).le (mass_positive last).le))
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact paid.trans_eq (by rw [← mul_inv_rev]; congr 1)

theorem column_low (wave : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ index ∈ F ∩ integerWaveFrequencyCube (radius wave), kernel index wave*density 3 index) ≤
      54*((radius wave : ℝ)*Real.sqrt (radius wave))⁻¹ := by
  have compared := Finset.sum_le_sum (s := F ∩ integerWaveFrequencyCube (radius wave))
    (fun index _ => mul_le_mul_of_nonneg_right (column_kernel index wave) (density_positive 3 index).le)
  rw [← Finset.mul_sum] at compared
  have paid := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right (s₁ := F))
    (fun index _ _ => (density_positive 3 index).le)).trans (prefix_three (radius wave) (radius_positive wave))
  apply compared.trans ((mul_le_mul_of_nonneg_left paid (by positivity)).trans_eq _)
  calc
    _ = 54*(Real.sqrt (radius wave)/(radius wave : ℝ)^2) := by
      field_simp [(Nat.cast_pos.mpr (radius_positive wave) : (0 : ℝ) < radius wave).ne']
    _ = _ := by rw [root_div_square _ (Nat.cast_pos.mpr (radius_positive wave))]

theorem column_high_point (first last : IntegerWavevector) :
    kernel first last*density 3 first ≤ density 2 last*density 7 first := by
  unfold kernel
  have paid := mul_le_mul_of_nonneg_left
    (inv_anti₀ (mass_positive first) (le_add_of_nonneg_right (mass_positive last).le)) (density_positive 2 last).le
  apply (mul_le_mul_of_nonneg_right paid (density_positive 3 first).le).trans_eq
  rw [← density_four, mul_assoc, ← density_add]

theorem column_bound (wave : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ index ∈ F, kernel index wave*density 3 index) ≤ 512*density 3 wave := by
  have compared := Finset.sum_le_sum (s := F \ integerWaveFrequencyCube (radius wave))
    (fun index _ => column_high_point index wave)
  rw [← Finset.mul_sum] at compared
  have high := compared.trans (mul_le_mul_of_nonneg_left
    (seven_tail (radius wave) (radius_positive wave) F) (density_positive 2 wave).le)
  have reduced := high.trans (mul_le_mul_of_nonneg_right (density_two_radius wave)
    (by positivity : 0 ≤ 52/Real.sqrt (radius wave)))
  have cap := mul_le_mul_of_nonneg_left (radius_density wave) (by norm_num : (0 : ℝ) ≤ 106)
  rw [← Finset.sum_inter_add_sum_sdiff F (integerWaveFrequencyCube (radius wave))]
  apply (add_le_add (column_low wave F) reduced).trans
  have same : (radius wave : ℝ)⁻¹*(52/Real.sqrt (radius wave)) =
      52*((radius wave : ℝ)*Real.sqrt (radius wave))⁻¹ := by ring
  rw [same]
  nlinarith [density_positive 3 wave]

theorem joint_control (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (NativeUnheatedSchur.term kernel left right) ∧
      (∑' index, NativeUnheatedSchur.term kernel left right index) ≤ 512*‖left‖*‖right‖ :=
  ⟨NativeUnheatedSchur.summable kernel (density 3) 512 kernel_nonnegative
    (density_positive 3) (by norm_num) row_bound column_bound left right,
   NativeUnheatedSchur.bound kernel (density 3) 512 kernel_nonnegative
    (density_positive 3) (by norm_num) row_bound column_bound left right⟩

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticHardy
