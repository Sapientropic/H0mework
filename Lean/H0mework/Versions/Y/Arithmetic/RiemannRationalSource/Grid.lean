import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.ReciprocalCells

/-! The canonical finite source partition of one actual reciprocal sampling channel. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open OriginalPaGreenContact
open scoped InnerProductSpace Topology
noncomputable section

def reciprocalSampleGridLength (n : ℕ) : ℕ := 4 * n - n / 4

def reciprocalSampleGrid (n : ℕ) : ℕ → ℝ
  | 0 => 4
  | j + 1 => (n : ℝ) / (n / 4 + j + 1 : ℕ)

@[simp] theorem reciprocal_sample_grid_zero (n : ℕ) :
    reciprocalSampleGrid n 0 = 4 := rfl

@[simp] theorem reciprocal_sample_grid_succ (n j : ℕ) :
    reciprocalSampleGrid n (j + 1) = (n : ℝ) / (n / 4 + j + 1 : ℕ) := rfl

theorem reciprocal_sample_grid_length_pos (n : ℕ) (positive : 0 < n) :
    0 < reciprocalSampleGridLength n := by
  dsimp only [reciprocalSampleGridLength]
  omega

theorem reciprocal_sample_grid_bounds (n : ℕ) (_positive : 0 < n)
    {j : ℕ} (bounded : j ≤ reciprocalSampleGridLength n) :
    reciprocalSampleGrid n j ∈ Icc (1 / 4) 4 := by
  cases j with
  | zero => norm_num
  | succ j =>
    have dp : (0 : ℝ) < (n / 4 + j + 1 : ℕ) := by positivity
    have low : n / 4 + j + 1 ≤ 4 * n := by
      dsimp only [reciprocalSampleGridLength] at bounded
      omega
    have high : n ≤ 4 * (n / 4 + j + 1) := by omega
    rw [reciprocal_sample_grid_succ]
    constructor
    · apply (le_div_iff₀ dp).mpr
      have castLow : ((n / 4 + j + 1 : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by
        exact_mod_cast low
      linarith
    · apply (div_le_iff₀ dp).mpr
      exact_mod_cast high

theorem reciprocal_sample_grid_antitone_step (n : ℕ) (positive : 0 < n)
    {j : ℕ} (bounded : j < reciprocalSampleGridLength n) :
    reciprocalSampleGrid n (j + 1) ≤ reciprocalSampleGrid n j := by
  cases j with
  | zero =>
    simpa using (reciprocal_sample_grid_bounds n positive (Nat.succ_le_of_lt bounded)).2
  | succ j =>
    simp only [reciprocal_sample_grid_succ]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity)
    exact_mod_cast (by omega : n / 4 + j + 1 ≤ n / 4 + (j + 1) + 1)

theorem reciprocal_sample_grid_last (n : ℕ) (positive : 0 < n) :
    reciprocalSampleGrid n (reciprocalSampleGridLength n) = 1 / 4 := by
  have lengthPositive := reciprocal_sample_grid_length_pos n positive
  obtain ⟨j, length⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt lengthPositive)
  rw [length, reciprocal_sample_grid_succ]
  have denominator : n / 4 + j + 1 = 4 * n := by
    dsimp only [reciprocalSampleGridLength] at length
    omega
  rw [denominator]
  push_cast
  have nonzero : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  field_simp

theorem reciprocal_sample_grid_cell (n : ℕ) (positive : 0 < n)
    {j : ℕ} (bounded : j < reciprocalSampleGridLength n) {t : ℝ}
    (inside : t ∈ Ioo (reciprocalSampleGrid n (j + 1)) (reciprocalSampleGrid n j)) :
    (n : ℝ) / t ∈ Ioo ((n / 4 + j : ℕ) : ℝ) ((n / 4 + j + 1 : ℕ) : ℝ) := by
  have lowerBound := (reciprocal_sample_grid_bounds n positive (Nat.succ_le_of_lt bounded)).1
  have tp : 0 < t := by linarith [inside.1]
  have dp : (0 : ℝ) < (n / 4 + j + 1 : ℕ) := by positivity
  have upper : (n : ℝ) / t < (n / 4 + j + 1 : ℕ) := by
    apply (div_lt_iff₀ tp).mpr
    have low : (n : ℝ) / (n / 4 + j + 1 : ℕ) < t := by
      simpa only [reciprocal_sample_grid_succ] using inside.1
    have scaled := (div_lt_iff₀ dp).mp low
    simpa only [mul_comm] using scaled
  refine ⟨?_, upper⟩
  cases j with
  | zero =>
    simp only [Nat.add_zero]
    apply (lt_div_iff₀ tp).mpr
    have bound : t < 4 := by simpa using inside.2
    have floorBound : 4 * (n / 4) ≤ n := by omega
    have floorCast : (4 : ℝ) * (n / 4 : ℕ) ≤ (n : ℝ) := by exact_mod_cast floorBound
    have np : (0 : ℝ) < n := by exact_mod_cast positive
    have kn : (0 : ℝ) ≤ (n / 4 : ℕ) := Nat.cast_nonneg _
    by_cases zero : n / 4 = 0
    · simp only [zero, Nat.cast_zero, zero_mul]
      exact np
    · have kp : (0 : ℝ) < (n / 4 : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero zero
      nlinarith
  | succ j =>
    apply (lt_div_iff₀ tp).mpr
    have kp : (0 : ℝ) < (n / 4 + j + 1 : ℕ) := by positivity
    have high : t < (n : ℝ) / (n / 4 + j + 1 : ℕ) := by
      simpa only [reciprocal_sample_grid_succ] using inside.2
    have scaled := (lt_div_iff₀ kp).mp high
    simpa only [Nat.add_assoc, mul_comm] using scaled

theorem reciprocal_sample_grid_raw_read (s : ℂ) (n : ℕ) (positive : 0 < n)
    {j : ℕ} (bounded : j < reciprocalSampleGridLength n) {t : ℝ}
    (inside : t ∈ Ioo (reciprocalSampleGrid n (j + 1)) (reciprocalSampleGrid n j)) :
    (t : ℂ)⁻¹ *
      (burnolUnitTailDirichletRaw s 1 ((n : ℝ) / t) -
        burnolUnitTailDirichletRaw (1 - s) 1 ((n : ℝ) / t)) =
      reciprocalSampleWave s n (n / 4 + j) t := by
  have cell := reciprocal_sample_grid_cell n positive bounded inside
  have read := cell_wave_read s (n / 4 + j) ⟨cell.1, by simpa using cell.2.le⟩
  exact congrArg (fun value => (t : ℂ)⁻¹ * value) read

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
