import H0mework.NavierStokes.StressMovingSource.ProductScalar

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeMovingCriticalProductWeights

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalIntegerLatticeCriticalKernel
open NativeMovingCriticalProductScalar

noncomputable section

def weight (wave : IntegerWavevector) : ℝ := integerWaveNormSq wave ^ (7 / 8 : ℝ)

theorem weight_nonnegative (wave : IntegerWavevector) : 0 ≤ weight wave :=
  Real.rpow_nonneg (integerWaveNormSq_nonneg wave) _

theorem weight_positive (wave : IntegerWavevector) (nonzero : wave ≠ 0) : 0 < weight wave :=
  Real.rpow_pos_of_pos (integerWaveNormSq_pos nonzero) _

theorem kernel_summable : Summable (fun wave => (weight wave)⁻¹ ^ 2) := by
  have lattice := ZLattice.summable_norm_rpow integerWaveZLattice (-7 / 2) (by
    rw [integerWaveZLattice_finrank]
    norm_num)
  rw [← integerWaveToZLattice.toEquiv.summable_iff] at lattice
  apply lattice.congr
  intro wave
  have normSquare : integerWaveNormSq wave = ‖integerWaveToZLattice wave‖ ^ (2 : ℝ) := by
    norm_num [← integerWaveToZLattice_norm_sq]
  rw [weight, normSquare, ← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_neg (norm_nonneg _), ← Real.rpow_mul_natCast (norm_nonneg _)]
  norm_num

def constant : ℝ := ∑' wave, (weight wave)⁻¹ ^ 2

theorem constant_nonnegative : 0 ≤ constant := tsum_nonneg fun _ => sq_nonneg _

theorem convolution_control (F : Finset IntegerWavevector) (zero : 0 ∉ F)
    (a b : IntegerWavevector → ℝ) :
    (∑ k ∈ F, convolution F a b k ^ 2) ≤ constant * mass F weight a * mass F weight b :=
  convolution_bound F weight a b weight_nonnegative
    (fun k member => weight_positive k (by rintro rfl; exact zero member)) kernel_summable

theorem dyadic_interpolation {ι : Type*} (F : Finset ι) (base a : ι → ℝ)
    (nonnegative : ∀ k, 0 ≤ base k) :
    (∑ k ∈ F, base k ^ 7 * a k ^ 2) ^ 8 ≤
      (∑ k ∈ F, a k ^ 2) * (∑ k ∈ F, base k ^ 8 * a k ^ 2) ^ 7 := by
  let m (n : ℕ) := ∑ k ∈ F, base k ^ n * a k ^ 2
  have positive (n : ℕ) : 0 ≤ m n := Finset.sum_nonneg fun k _ => by
    exact mul_nonneg (pow_nonneg (nonnegative k) _) (sq_nonneg _)
  have cauchy (n : ℕ) : m (n + 4) ^ 2 ≤ m (2 * n) * m 8 := by
    have bound := Finset.sum_mul_sq_le_sq_mul_sq F (fun k => base k ^ n * a k)
      (fun k => base k ^ 4 * a k)
    have middle : (∑ k ∈ F, base k ^ n * a k * (base k ^ 4 * a k)) = m (n + 4) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
      ring
    have sides (n : ℕ) : (∑ k ∈ F, (base k ^ n * a k) ^ 2) = m (2 * n) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow, ← pow_mul, Nat.mul_comm]
    rw [middle, sides, sides] at bound
    exact bound
  have h7 : m 7 ^ 2 ≤ m 6 * m 8 := by simpa using cauchy 3
  have h6 : m 6 ^ 2 ≤ m 4 * m 8 := by simpa using cauchy 2
  have h4 : m 4 ^ 2 ≤ m 0 * m 8 := by simpa using cauchy 0
  have fourth : m 7 ^ 4 ≤ m 4 * m 8 ^ 3 := by
    calc
      _ = (m 7 ^ 2) ^ 2 := by ring
      _ ≤ (m 6 * m 8) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h7 _
      _ = m 6 ^ 2 * m 8 ^ 2 := mul_pow ..
      _ ≤ (m 4 * m 8) * m 8 ^ 2 := mul_le_mul_of_nonneg_right h6 (sq_nonneg _)
      _ = _ := by ring
  have eighth : m 7 ^ 8 ≤ m 0 * m 8 ^ 7 := by
    calc
      _ = (m 7 ^ 4) ^ 2 := by ring
      _ ≤ (m 4 * m 8 ^ 3) ^ 2 := pow_le_pow_left₀ (pow_nonneg (positive 7) _) fourth _
      _ = m 4 ^ 2 * m 8 ^ 6 := by ring
      _ ≤ (m 0 * m 8) * m 8 ^ 6 := mul_le_mul_of_nonneg_right h4 (pow_nonneg (positive 8) _)
      _ = _ := by ring
  simpa only [m, pow_zero, one_mul] using eighth

theorem mass_interpolation (F : Finset IntegerWavevector) (a : IntegerWavevector → ℝ) :
    mass F weight a ^ 8 ≤ (∑ k ∈ F, a k ^ 2) * mass F integerWaveNormSq a ^ 7 := by
  have bound := dyadic_interpolation F (fun k => integerWaveNormSq k ^ (1 / 8 : ℝ)) a
    (fun k => Real.rpow_nonneg (integerWaveNormSq_nonneg k) _)
  have powers (k : IntegerWavevector) (n : ℕ) :
      (integerWaveNormSq k ^ (1 / 8 : ℝ)) ^ n = integerWaveNormSq k ^ ((n : ℝ) / 8) := by
    rw [← Real.rpow_mul_natCast (integerWaveNormSq_nonneg k)]
    congr 1
    ring
  simp only [powers] at bound
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (8 : ℝ) ≠ 0), Real.rpow_one] at bound
  exact bound

end
end SaturationMonoid.NavierStokes.NativeMovingCriticalProductWeights
