import H0mework.Versions.X.NavierStokes.HigherTreeSexticUniform.Cube
import Mathlib.Data.Nat.Log

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformPrefix
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeUnheatedSexticLatticePower NativeUnheatedClockMomentKernel NativeUnheatedSexticUniformCube
noncomputable section

def amount (power : ℕ) (center : IntegerWavevector) (radius : ℕ) : ℝ :=
  ∑ wave ∈ integerWaveFrequencyCube radius, density power wave*density 2 (center-wave)

theorem amount_nonnegative (power : ℕ) (center : IntegerWavevector) (radius : ℕ) : 0 ≤ amount power center radius :=
  Finset.sum_nonneg fun wave _ => mul_nonneg (density_positive power wave).le (density_positive 2 (center-wave)).le

theorem amount_mono (power : ℕ) (center : IntegerWavevector) {first last : ℕ} (ordered : first ≤ last) :
    amount power center first ≤ amount power center last :=
  Finset.sum_le_sum_of_subset_of_nonneg (cube_mono ordered) (fun wave _ _ => mul_nonneg (density_positive power wave).le (density_positive 2 (center-wave)).le)

theorem annulus_three (center : IntegerWavevector) (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube (4*radius) \ integerWaveFrequencyCube radius,
      density 3 wave*density 2 (center-wave)) ≤ 2160*Real.sqrt radius := by
  apply (annulus_bound 3 center radius positive).trans_eq
  have root : 0 < Real.sqrt radius := Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)
  have fourth : (Real.sqrt radius)^4 = (radius : ℝ)^2 := by
    rw [show (Real.sqrt radius)^4 = ((Real.sqrt radius)^2)^2 by ring, Real.sq_sqrt (Nat.cast_nonneg radius)]
  push_cast
  field_simp
  linear_combination -2160*fourth

theorem step (center : IntegerWavevector) (radius : ℕ) (positive : 0 < radius) :
    amount 3 center (4*radius) ≤ amount 3 center radius+2160*Real.sqrt radius := by
  rw [amount, ← Finset.sum_sdiff (cube_mono (show radius ≤ 4*radius by omega))]
  exact (add_le_add (annulus_three center radius positive) (le_rfl : amount 3 center radius ≤ amount 3 center radius)).trans_eq (by ring)

theorem base (center : IntegerWavevector) : amount 3 center 1 ≤ 2160 := by
  have point (wave : IntegerWavevector) : density 3 wave*density 2 (center-wave) ≤ density 2 (center-wave) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (density_le_one 3 wave) (density_positive 2 (center-wave)).le
  have paid := (Finset.sum_le_sum (s := integerWaveFrequencyCube 1) fun wave _ => point wave).trans
    (translated_sum center 1 (by decide))
  norm_num only [Nat.cast_one, one_pow, mul_one] at paid
  exact paid.trans (by norm_num)

theorem power_bound (center : IntegerWavevector) (number : ℕ) : amount 3 center (4^number) ≤ 2160*Real.sqrt (4^number : ℕ) := by
  induction number with
  | zero => simpa using base center
  | succ number previous =>
      have same : (4 : ℕ)^(number+1)=4*4^number := by rw [pow_succ, Nat.mul_comm]
      rw [same]
      apply ((step center (4^number) (by positivity)).trans (add_le_add previous (le_rfl : 2160*Real.sqrt (4^number : ℕ) ≤ 2160*Real.sqrt (4^number : ℕ)))).trans_eq
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring

theorem weighted_prefix (center : IntegerWavevector) (radius : ℕ) (positive : 0 < radius) :
    amount 3 center radius ≤ 4320*Real.sqrt radius := by
  let number := Nat.log 4 radius+1
  have inside : radius ≤ 4^number := (Nat.lt_pow_succ_log_self (by norm_num : 1 < (4 : ℕ)) radius).le
  have upper : 4^number ≤ 4*radius := by
    rw [show 4^number = 4*4^(Nat.log 4 radius) by dsimp only [number]; rw [pow_succ, Nat.mul_comm]]
    exact Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 4 (Nat.ne_of_gt positive))
  have compared := (amount_mono 3 center inside).trans (power_bound center number)
  have paid := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr upper)) (by norm_num : (0 : ℝ) ≤ 2160)
  apply compared.trans (paid.trans_eq _)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformPrefix
