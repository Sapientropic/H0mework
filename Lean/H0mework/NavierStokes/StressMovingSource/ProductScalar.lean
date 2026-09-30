import H0mework.NavierStokes.Fourier.IntegerLatticeCriticalKernel
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeMovingCriticalProductScalar

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore

noncomputable section

def convolution (F : Finset IntegerWavevector) (a b : IntegerWavevector → ℝ) (k : IntegerWavevector) : ℝ :=
  ∑ p ∈ F, if k - p ∈ F then a p * b (k - p) else 0

theorem translated_sum_le (F : Finset IntegerWavevector) (f : IntegerWavevector → ℝ)
    (nonnegative : ∀ k, 0 ≤ f k) (map : IntegerWavevector → IntegerWavevector)
    (injective : Function.Injective map) :
    (∑ k ∈ F, if map k ∈ F then f (map k) else 0) ≤ ∑ k ∈ F, f k := by
  rw [← Finset.sum_filter]
  have subset : (F.filter fun k => map k ∈ F).image map ⊆ F := by
    intro k member
    obtain ⟨p, selected, rfl⟩ := Finset.mem_image.mp member
    exact (Finset.mem_filter.mp selected).2
  calc
    _ = ∑ k ∈ (F.filter fun k => map k ∈ F).image map, f k := by
      rw [Finset.sum_image (fun p _ q _ same => injective same)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg subset (fun k _ _ => nonnegative k)

def kernel (F : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ) (k : IntegerWavevector) : ℝ :=
  ∑ p ∈ F, if k - p ∈ F then (weight p)⁻¹ * (weight (k - p))⁻¹ else 0

theorem kernel_bound (F : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ)
    (nonnegative : ∀ k, 0 ≤ weight k) (summable : Summable (fun k => (weight k)⁻¹ ^ 2)) (k : IntegerWavevector) :
    kernel F weight k ≤ ∑' p, (weight p)⁻¹ ^ 2 := by
  have first := summable.sum_le_tsum F (fun p _ => sq_nonneg ((weight p)⁻¹))
  have second : (∑ p ∈ F, (if k - p ∈ F then (weight (k - p))⁻¹ else 0) ^ 2) ≤
      ∑' p, (weight p)⁻¹ ^ 2 := by
    simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
    exact (translated_sum_le F (fun p => (weight p)⁻¹ ^ 2) (fun _ => sq_nonneg _)
      (fun p => k - p) sub_right_injective).trans first
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq F
    (fun p => (weight p)⁻¹) (fun p => if k - p ∈ F then (weight (k - p))⁻¹ else 0)
  have squared : kernel F weight k ^ 2 ≤ (∑' p, (weight p)⁻¹ ^ 2) ^ 2 := by
    calc
      _ ≤ (∑ p ∈ F, (weight p)⁻¹ ^ 2) *
          ∑ p ∈ F, (if k - p ∈ F then (weight (k - p))⁻¹ else 0) ^ 2 := by
        simpa only [kernel, mul_ite, mul_zero] using cauchy
      _ ≤ (∑' p, (weight p)⁻¹ ^ 2) * (∑' p, (weight p)⁻¹ ^ 2) :=
        mul_le_mul first second (Finset.sum_nonneg fun _ _ => sq_nonneg _) (tsum_nonneg fun _ => sq_nonneg _)
      _ = _ := (pow_two _).symm
  have kernel_nonnegative : 0 ≤ kernel F weight k := by
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr (nonnegative p)) (inv_nonneg.mpr (nonnegative (k - p)))
    · exact le_rfl
  exact (sq_le_sq₀ kernel_nonnegative (tsum_nonneg fun _ => sq_nonneg _)).mp squared

def mass (F : Finset IntegerWavevector) (weight a : IntegerWavevector → ℝ) : ℝ :=
  ∑ p ∈ F, weight p * a p ^ 2

/-- Output amplitudes are summed before squaring. The complete interference survives both Cauchy steps. -/
theorem convolution_bound (F : Finset IntegerWavevector) (weight a b : IntegerWavevector → ℝ)
    (nonnegative : ∀ k, 0 ≤ weight k) (positive : ∀ k ∈ F, 0 < weight k)
    (summable : Summable (fun k => (weight k)⁻¹ ^ 2)) :
    (∑ k ∈ F, convolution F a b k ^ 2) ≤
      (∑' p, (weight p)⁻¹ ^ 2) * mass F weight a * mass F weight b := by
  let term (k p : IntegerWavevector) :=
    if k - p ∈ F then (weight p * a p ^ 2) * (weight (k - p) * b (k - p) ^ 2) else 0
  have term_nonnegative (k p : IntegerWavevector) : 0 ≤ term k p := by
    dsimp only [term]
    split_ifs
    · exact mul_nonneg (mul_nonneg (nonnegative p) (sq_nonneg _))
        (mul_nonneg (nonnegative (k - p)) (sq_nonneg _))
    · exact le_rfl
  have row (k : IntegerWavevector) : convolution F a b k ^ 2 ≤
      (∑' p, (weight p)⁻¹ ^ 2) * ∑ p ∈ F, term k p := by
    have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul F
      (r := fun p => if k - p ∈ F then a p * b (k - p) else 0)
      (f := fun p => if k - p ∈ F then (weight p)⁻¹ * (weight (k - p))⁻¹ else 0)
      (g := term k)
      (fun p _ => by
        split_ifs
        · exact mul_nonneg (inv_nonneg.mpr (nonnegative p)) (inv_nonneg.mpr (nonnegative (k - p)))
        · exact le_rfl)
      (fun p _ => term_nonnegative k p)
      (fun p member => by
        dsimp only [term]
        by_cases inside : k - p ∈ F
        · simp only [if_pos inside]
          apply le_of_eq
          field_simp [(positive p member).ne', (positive (k - p) inside).ne']
        · simp [inside])
    exact cauchy.trans (mul_le_mul_of_nonneg_right (kernel_bound F weight nonnegative summable k)
      (Finset.sum_nonneg fun p _ => term_nonnegative k p))
  have aggregate : (∑ k ∈ F, ∑ p ∈ F, term k p) ≤ mass F weight a * mass F weight b := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ p ∈ F, (weight p * a p ^ 2) * mass F weight b := by
        apply Finset.sum_le_sum
        intro p member
        have factor : (∑ k ∈ F, term k p) = (weight p * a p ^ 2) *
            ∑ k ∈ F, if k - p ∈ F then weight (k - p) * b (k - p) ^ 2 else 0 := by
          simp only [term, Finset.mul_sum, mul_ite, mul_zero]
        rw [factor]
        exact mul_le_mul_of_nonneg_left
          (translated_sum_le F (fun q => weight q * b q ^ 2)
            (fun q => mul_nonneg (nonnegative q) (sq_nonneg _)) (fun k => k - p)
            sub_left_injective) (mul_nonneg (nonnegative p) (sq_nonneg _))
      _ = _ := (Finset.sum_mul ..).symm
  calc
    _ ≤ ∑ k ∈ F, (∑' p, (weight p)⁻¹ ^ 2) * ∑ p ∈ F, term k p := Finset.sum_le_sum fun k _ => row k
    _ = (∑' p, (weight p)⁻¹ ^ 2) * (∑ k ∈ F, ∑ p ∈ F, term k p) := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left aggregate (tsum_nonneg fun _ => sq_nonneg _)

end
end SaturationMonoid.NavierStokes.NativeMovingCriticalProductScalar
