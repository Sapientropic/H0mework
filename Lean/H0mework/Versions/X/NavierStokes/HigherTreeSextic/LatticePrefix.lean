import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticePower

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticLatticePrefix
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeCompleteStressCarrier NativeUnheatedRieszKernel NativeUnheatedClockMomentKernel
open NativeUnheatedSexticLatticePower
noncomputable section

theorem density_small (power : ℕ) (small : power ≤ 4) (wave : IntegerWavevector) :
    density power wave = density 4 wave*radical wave^(4-power) := by
  unfold density
  field_simp [(radical_positive wave).ne']
  rw [← pow_add, Nat.add_sub_of_le small]

theorem prefix_small (power : ℕ) (small : power ≤ 4) (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube radius, density power wave) ≤
      27*(radius : ℝ)*(2*Real.sqrt radius)^(4-power) := by
  have rows (wave : IntegerWavevector) (inside : wave ∈ integerWaveFrequencyCube radius) :
      density power wave ≤ weight wave*(2*Real.sqrt radius)^(4-power) := by
    rw [density_small power small wave]
    exact mul_le_mul (density_four_le_weight wave)
      (pow_le_pow_left₀ (radical_positive wave).le (radical_cube_upper radius positive wave inside) (4-power))
      (pow_nonneg (radical_positive wave).le _) (weight_pos wave).le
  have compared := Finset.sum_le_sum rows
  rw [← Finset.sum_mul] at compared
  have atLeast : (1 : ℝ) ≤ radius := by exact_mod_cast positive
  have paid := mul_le_mul_of_nonneg_right (cube_weight_sum radius) (by positivity : 0 ≤ (2*Real.sqrt radius)^(4-power))
  exact compared.trans (paid.trans (by gcongr; linarith))

theorem prefix_one (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube radius, density 1 wave) ≤ 216*(radius : ℝ)^2*Real.sqrt radius := by
  apply (prefix_small 1 (by omega) radius positive).trans_eq
  norm_num only
  linear_combination 216*(radius : ℝ)*Real.sqrt radius*(Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) radius))

theorem prefix_two (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube radius, density 2 wave) ≤ 108*(radius : ℝ)^2 := by
  apply (prefix_small 2 (by omega) radius positive).trans_eq
  norm_num only
  linear_combination 108*(radius : ℝ)*(Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) radius))

theorem prefix_three (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube radius, density 3 wave) ≤ 54*(radius : ℝ)*Real.sqrt radius := by
  apply (prefix_small 3 (by omega) radius positive).trans_eq
  norm_num only
  ring

theorem shell_five (radius : ℕ) :
    (∑ wave ∈ shell radius, density 5 wave) ≤ 26/Real.sqrt ((radius : ℝ)+1) := by
  have rows (wave : IntegerWavevector) (inside : wave ∈ shell radius) :
      density 5 wave ≤ (integerWaveNormSq wave)⁻¹*(Real.sqrt ((radius : ℝ)+1))⁻¹ := by
    have lower := shell_frequency radius wave inside
    have normPositive : 0 < integerWaveNormSq wave := lt_of_lt_of_le (by positivity) lower
    have root := radical_lower (radius+1) wave (lower.trans (by unfold mass; linarith))
    simp only [Nat.cast_add, Nat.cast_one] at root
    rw [show (5 : ℕ) = 4+1 by norm_num, density_add, density_four]
    simp only [density, pow_one]
    exact mul_le_mul (inv_anti₀ normPositive (by unfold mass; linarith))
      (inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) root)
      (inv_nonneg.mpr (radical_positive wave).le) (inv_nonneg.mpr normPositive.le)
  have paid := Finset.sum_le_sum rows
  rw [← Finset.sum_mul] at paid
  exact paid.trans ((mul_le_mul_of_nonneg_right (shell_inverse_sum radius) (by positivity)).trans_eq (by ring))

theorem root_increment (number : ℕ) :
    (Real.sqrt ((number : ℝ)+1))⁻¹ ≤ 2*(Real.sqrt ((number : ℝ)+1)-Real.sqrt number) := by
  have positive : 0 < Real.sqrt ((number : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have first := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) number)
  have last := Real.sq_sqrt (show 0 ≤ (number : ℝ)+1 by positivity)
  have paid : 1 ≤ (2*(Real.sqrt ((number : ℝ)+1)-Real.sqrt number))*Real.sqrt ((number : ℝ)+1) := by
    nlinarith [sq_nonneg (Real.sqrt ((number : ℝ)+1)-Real.sqrt number)]
  simpa only [one_mul] using (mul_le_mul_of_nonneg_right paid (inv_nonneg.mpr positive.le)).trans_eq (by
    rw [mul_assoc, mul_inv_cancel₀ positive.ne', mul_one])

theorem prefix_five_raw (radius : ℕ) :
    (∑ wave ∈ integerWaveFrequencyCube radius, density 5 wave) ≤ 1+52*Real.sqrt radius := by
  induction radius with
  | zero =>
      have cube : integerWaveFrequencyCube 0 = {0} := by
        ext wave
        simp only [integerWaveFrequencyCube, Fintype.mem_piFinset, Finset.mem_Icc, Int.natCast_zero, neg_zero, Finset.mem_singleton]
        constructor
        · intro member; funext coordinate; exact le_antisymm (member coordinate).2 (member coordinate).1
        · intro zero; subst wave; simp
      simp [cube, density, radical, mass, integerWaveNormSq]
  | succ radius previous =>
      rw [← Finset.sum_sdiff (cube_mono (Nat.le_succ radius))]
      have paid := add_le_add (shell_five radius) previous
      have increment := mul_le_mul_of_nonneg_left (root_increment radius) (by norm_num : (0 : ℝ) ≤ 26)
      push_cast
      apply paid.trans
      simp only [div_eq_mul_inv]
      linarith

theorem prefix_five (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube radius, density 5 wave) ≤ 53*Real.sqrt radius := by
  have atLeast : (1 : ℝ) ≤ radius := by exact_mod_cast positive
  have root : 1 ≤ Real.sqrt radius := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg radius)).mpr (by simpa using atLeast)
  exact (prefix_five_raw radius).trans (by linarith)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticLatticePrefix
