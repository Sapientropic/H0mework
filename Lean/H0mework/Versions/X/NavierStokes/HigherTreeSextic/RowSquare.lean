import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticePower

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticRowSquare
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open NativeUnheatedClockMomentKernel NativeUnheatedRieszKernel NativeUnheatedSexticLatticePower
noncomputable section

def pairMass (b c : IntegerWavevector) : ℝ := mass b+mass c
def pairRadius (b c : IntegerWavevector) : ℕ := max (radius b) (radius c)

theorem pairMass_positive (b c : IntegerWavevector) : 0 < pairMass b c :=
  add_pos (mass_positive b) (mass_positive c)

theorem pairRadius_positive (b c : IntegerWavevector) : 0 < pairRadius b c :=
  (radius_positive b).trans_le (le_max_left _ _)

theorem pair_lower (b c : IntegerWavevector) : ((pairRadius b c : ℕ) : ℝ)^2 ≤ pairMass b c := by
  rcases le_total (radius b) (radius c) with ordered | ordered
  · rw [pairRadius, max_eq_right ordered]
    exact (radius_lower c).trans (le_add_of_nonneg_left (mass_positive b).le)
  · rw [pairRadius, max_eq_left ordered]
    exact (radius_lower b).trans (le_add_of_nonneg_right (mass_positive c).le)

theorem pair_upper (b c : IntegerWavevector) : pairMass b c ≤ 8*(pairRadius b c : ℝ)^2 := by
  have one : (1 : ℝ) ≤ pairRadius b c := by exact_mod_cast pairRadius_positive b c
  have first := integerWaveNormSq_le_three_mul_radius_sq_of_mem (pairRadius b c) b
    (cube_mono (le_max_left _ _) (radius_member b))
  have last := integerWaveNormSq_le_three_mul_radius_sq_of_mem (pairRadius b c) c
    (cube_mono (le_max_right _ _) (radius_member c))
  unfold pairMass mass
  nlinarith

def decay (value : ℝ) : ℝ := (value^2*Real.sqrt value)⁻¹

theorem decay_nonnegative (value : ℝ) : 0 ≤ decay value :=
  inv_nonneg.mpr (mul_nonneg (sq_nonneg value) (Real.sqrt_nonneg value))

theorem near_point (b c r : IntegerWavevector) :
    decay (pairMass b c+mass r) ≤ ((pairMass b c)^2*(pairRadius b c : ℝ))⁻¹ := by
  have pair0 := pairMass_positive b c
  have radius0 : (0 : ℝ) < pairRadius b c := Nat.cast_pos.mpr (pairRadius_positive b c)
  have ordered : pairMass b c ≤ pairMass b c+mass r := le_add_of_nonneg_right (mass_positive r).le
  have root : (pairRadius b c : ℝ) ≤ Real.sqrt (pairMass b c+mass r) :=
    (Real.le_sqrt radius0.le (pair0.le.trans ordered)).mpr ((pair_lower b c).trans ordered)
  exact inv_anti₀ (mul_pos (sq_pos_of_pos pair0) radius0)
    (mul_le_mul (pow_le_pow_left₀ pair0.le ordered 2) root radius0.le (sq_nonneg _))

theorem near_sum (b c : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F ∩ integerWaveFrequencyCube (pairRadius b c), decay (pairMass b c+mass r)) ≤ 27/pairMass b c := by
  have pair0 := pairMass_positive b c
  have radius0 : (0 : ℝ) < pairRadius b c := Nat.cast_pos.mpr (pairRadius_positive b c)
  have full := Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right (s₁ := F)
    (s₂ := integerWaveFrequencyCube (pairRadius b c))) (fun r _ _ => decay_nonnegative (pairMass b c+mass r))
  have point := Finset.sum_le_sum (s := integerWaveFrequencyCube (pairRadius b c)) (fun r _ => near_point b c r)
  have count : ((integerWaveFrequencyCube (pairRadius b c)).card : ℝ) ≤ 27*(pairRadius b c : ℝ)^3 := by
    rw [integerWaveFrequencyCube_card]
    push_cast
    have one : (1 : ℝ) ≤ pairRadius b c := by exact_mod_cast pairRadius_positive b c
    have bounded : 2*(pairRadius b c : ℝ)+1 ≤ 3*(pairRadius b c : ℝ) := by linarith
    convert! pow_le_pow_left₀ (by positivity) bounded 3 using 1
    ring
  simp only [Finset.sum_const, nsmul_eq_mul] at point
  have paid := (full.trans point).trans (mul_le_mul_of_nonneg_right count (by positivity))
  apply paid.trans
  calc
    _ = 27*(pairRadius b c : ℝ)^2/(pairMass b c)^2 := by field_simp [pair0.ne', radius0.ne']
    _ ≤ 27*pairMass b c/(pairMass b c)^2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pair_lower b c) (by norm_num)) (sq_nonneg _)
    _ = _ := by field_simp [pair0.ne']

theorem far_point (b c r : IntegerWavevector) (outside : r ∉ integerWaveFrequencyCube (pairRadius b c)) :
    decay (pairMass b c+mass r) ≤ integerWaveCriticalKernel r/(pairRadius b c : ℝ) := by
  have radius0 : (0 : ℝ) < pairRadius b c := Nat.cast_pos.mpr (pairRadius_positive b c)
  have lower := outside_square (pairRadius b c) r outside
  have wave0 : 0 < integerWaveNormSq r := (sq_pos_of_pos radius0).trans_le lower
  have ordered : integerWaveNormSq r ≤ pairMass b c+mass r := by unfold mass; linarith [pairMass_positive b c]
  have root : (pairRadius b c : ℝ) ≤ Real.sqrt (pairMass b c+mass r) :=
    (Real.le_sqrt radius0.le (wave0.le.trans ordered)).mpr (lower.trans ordered)
  apply (inv_anti₀ (mul_pos (sq_pos_of_pos wave0) radius0)
    (mul_le_mul (pow_le_pow_left₀ wave0.le ordered 2) root radius0.le (sq_nonneg _))).trans_eq
  unfold integerWaveCriticalKernel
  ring

theorem far_sum (b c : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F \ integerWaveFrequencyCube (pairRadius b c), decay (pairMass b c+mass r)) ≤ 208/pairMass b c := by
  have pair0 := pairMass_positive b c
  have radius0 : (0 : ℝ) < pairRadius b c := Nat.cast_pos.mpr (pairRadius_positive b c)
  have compared := Finset.sum_le_sum (s := F \ integerWaveFrequencyCube (pairRadius b c))
    (fun r inside => far_point b c r (Finset.mem_sdiff.mp inside).2)
  rw [← Finset.sum_div] at compared
  have paid := compared.trans (div_le_div_of_nonneg_right
    (finiteModes_integerWaveCriticalKernel_tail_le (pairRadius b c) (pairRadius_positive b c) F) radius0.le)
  apply paid.trans
  rw [show (26*(pairRadius b c : ℝ)⁻¹)/(pairRadius b c : ℝ) = 26/(pairRadius b c : ℝ)^2 by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos radius0) pair0).mpr
  linarith [pair_upper b c]

theorem decay_sum (b c : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F, decay (pairMass b c+mass r)) ≤ 256/pairMass b c := by
  rw [← Finset.sum_inter_add_sum_sdiff F (integerWaveFrequencyCube (pairRadius b c))]
  have paid := add_le_add (near_sum b c F) (far_sum b c F)
  apply paid.trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (pairMass_positive b c).le

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticRowSquare
