import H0mework.Versions.X.NavierStokes.HigherTreeSextic.RowSquare
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticeTail

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticWeightedSquare
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeCompleteStressCarrier NativeUnheatedRieszKernel NativeUnheatedSexticLatticePower
open NativeUnheatedSexticRowSquare NativeUnheatedSexticLatticeTail
noncomputable section

theorem decay_antitone {small large : ℝ} (positive : 0 < small) (ordered : small ≤ large) :
    decay large ≤ decay small :=
  inv_anti₀ (mul_pos (sq_pos_of_pos positive) (Real.sqrt_pos.mpr positive))
    (mul_le_mul (pow_le_pow_left₀ positive.le ordered 2) (Real.sqrt_le_sqrt ordered)
      (Real.sqrt_nonneg _) (sq_nonneg _))

theorem density_ten (wave : IntegerWavevector) : density 10 wave = decay (mass wave) := by
  rw [density, show radical wave^10 = (radical wave^4)^2*radical wave^2 by ring,
    radical_fourth, radical_square]
  rfl

theorem point_bound (a b r : IntegerWavevector) :
    density 4 r*decay (pairMass a b+mass r) ≤ density 14 r := by
  have lower : mass r ≤ pairMass a b+mass r := le_add_of_nonneg_left (pairMass_positive a b).le
  apply (mul_le_mul_of_nonneg_left (decay_antitone (mass_positive r) lower) (density_positive 4 r).le).trans_eq
  rw [← density_ten, ← density_add]

theorem five_outside (R : ℕ) (positive : 0 < R) (r : IntegerWavevector)
    (outside : r ∉ integerWaveFrequencyCube R) : density 5 r ≤ ((R : ℝ)^2*Real.sqrt R)⁻¹ := by
  have root0 : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)
  have lower := radical_lower R r ((outside_square R r outside).trans (by unfold mass; linarith))
  have power := pow_le_pow_left₀ root0.le lower 5
  have identity : (Real.sqrt (R : ℝ))^5 = (R : ℝ)^2*Real.sqrt R := by
    rw [show (Real.sqrt (R : ℝ))^5 = ((Real.sqrt (R : ℝ))^2)^2*Real.sqrt R by ring,
      Real.sq_sqrt (Nat.cast_nonneg R)]
  simpa only [density, identity] using inv_anti₀ (pow_pos root0 5) power

theorem near_sum (a b : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F ∩ integerWaveFrequencyCube (pairRadius a b), density 4 r*decay (pairMass a b+mass r)) ≤
      27/(pairMass a b)^2 := by
  have B0 := pairMass_positive a b
  have R0 : (0 : ℝ) < pairRadius a b := Nat.cast_pos.mpr (pairRadius_positive a b)
  have rows := Finset.sum_le_sum (s := F ∩ integerWaveFrequencyCube (pairRadius a b))
    (fun r _ => mul_le_mul_of_nonneg_left (NativeUnheatedSexticRowSquare.near_point a b r) (density_positive 4 r).le)
  rw [← Finset.sum_mul] at rows
  have weighted := (Finset.sum_le_sum (s := F ∩ integerWaveFrequencyCube (pairRadius a b))
    (fun r _ => density_four_le_weight r)).trans
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right (s₁ := F))
      (fun r _ _ => (weight_pos r).le)).trans (cube_weight_sum _))
  have one : (1 : ℝ) ≤ pairRadius a b := by exact_mod_cast pairRadius_positive a b
  have budget : (∑ r ∈ F ∩ integerWaveFrequencyCube (pairRadius a b), density 4 r) ≤ 27*(pairRadius a b : ℝ) :=
    weighted.trans (by linarith)
  exact rows.trans ((mul_le_mul_of_nonneg_right budget (by positivity)).trans_eq
    (by field_simp [B0.ne', R0.ne']))

theorem far_sum (a b : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F \ integerWaveFrequencyCube (pairRadius a b), density 4 r*decay (pairMass a b+mass r)) ≤
      1664/(pairMass a b)^2 := by
  have B0 := pairMass_positive a b
  have R0 : (0 : ℝ) < pairRadius a b := Nat.cast_pos.mpr (pairRadius_positive a b)
  have sqrt0 : 0 < Real.sqrt (pairRadius a b : ℝ) := Real.sqrt_pos.mpr R0
  have point (r : IntegerWavevector) (outside : r ∉ integerWaveFrequencyCube (pairRadius a b)) :
      density 4 r*decay (pairMass a b+mass r) ≤ density 9 r*((pairRadius a b : ℝ)^2*Real.sqrt (pairRadius a b))⁻¹ := by
    apply (point_bound a b r).trans
    rw [show 14 = 9+5 by omega, density_add]
    exact mul_le_mul_of_nonneg_left (five_outside (pairRadius a b) (pairRadius_positive a b) r outside) (density_positive 9 r).le
  have compared := Finset.sum_le_sum (s := F \ integerWaveFrequencyCube (pairRadius a b))
    (fun r inside => point r (Finset.mem_sdiff.mp inside).2)
  rw [← Finset.sum_mul] at compared
  have paid := compared.trans (mul_le_mul_of_nonneg_right
    (nine_tail (pairRadius a b) (pairRadius_positive a b) F) (by positivity))
  apply paid.trans
  calc
    _ = 26/(pairRadius a b : ℝ)^4 := by
      have root := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (pairRadius a b))
      field_simp [R0.ne', sqrt0.ne']
      nlinarith [root]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (pow_pos R0 4) (sq_pos_of_pos B0)).mpr
      have squared := pow_le_pow_left₀ B0.le (pair_upper a b) 2
      nlinarith only [squared]

theorem finite_bound (a b : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F, density 4 r*decay (pairMass a b+mass r)) ≤ 4096/(pairMass a b)^2 := by
  rw [← Finset.sum_inter_add_sum_sdiff F (integerWaveFrequencyCube (pairRadius a b))]
  apply (add_le_add (near_sum a b F) (far_sum a b F)).trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticWeightedSquare
