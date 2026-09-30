import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticePower
import H0mework.NavierStokes.HigherTreeSextic.Schur

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeRieszKernel
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativeUnheatedSexticLatticePower NativeUnheatedSchur
noncomputable section

abbrev Wave := IntegerWavevector
abbrev E := Space Wave

def kernel (k p : Wave) : ℝ := radical k*density 2 p*density 2 (k-p)

theorem kernel_nonnegative (k p : Wave) : 0 ≤ kernel k p := by
  unfold kernel
  positivity [radical_positive k, density_positive 2 p, density_positive 2 (k-p)]

theorem kernel_square_sum (k : Wave) (F : Finset Wave) :
    (∑ p ∈ F, kernel k p^2) ≤ NativeUnheatedRieszKernel.constant := by
  have density_square (p : Wave) : density 2 p^2 = density 4 p := by
    rw [show (4 : ℕ) = 2+2 from rfl, density_add, pow_two]
  calc
    _ = radical k^2*(∑ p ∈ F, density 4 p*density 4 (k-p)) := by
      simp only [kernel, mul_pow, density_square, Finset.mul_sum, mul_assoc]
    _ ≤ radical k^2*(∑ p ∈ F, NativeCompleteStressCarrier.weight p*
        NativeCompleteStressCarrier.weight (k-p)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun p _ => mul_le_mul (density_four_le_weight p)
        (density_four_le_weight (k-p)) (density_positive 4 (k-p)).le
        (NativeCompleteStressCarrier.weight_pos p).le
    _ ≤ _ := by
      rw [radical_square]
      exact NativeUnheatedRieszKernel.finite_bound k F

def term (L M T : E) (index : Wave × Wave) : ℝ :=
  kernel index.1 index.2*|L index.2| *|M (index.1-index.2)| *|T index.1|

theorem term_nonnegative (L M T : E) (index : Wave × Wave) : 0 ≤ term L M T index := by
  unfold term
  positivity [kernel_nonnegative index.1 index.2]

theorem translated_square_sum (M : E) (p : Wave) (F : Finset Wave) :
    (∑ k ∈ F, |M (k-p)|^2) ≤ ‖M‖^2 := by
  classical
  have paid := square_sum_le M (F.image (fun k => k-p))
  rw [Finset.sum_image (fun _ _ _ _ equal => sub_left_injective equal)] at paid
  exact paid

theorem rectangle_bound (L M T : E) (S F : Finset Wave) :
    (∑ index ∈ S ×ˢ F, term L M T index) ≤
      Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by
  let a : Wave × Wave → ℝ := fun index => kernel index.1 index.2*|T index.1|
  let b : Wave × Wave → ℝ := fun index => |L index.2| *|M (index.1-index.2)|
  have first : (∑ index ∈ S ×ˢ F, a index^2) ≤ NativeUnheatedRieszKernel.constant*‖T‖^2 := by
    rw [Finset.sum_product]
    calc
      _ = ∑ k ∈ S, (∑ p ∈ F, kernel k p^2)*|T k|^2 := by
        simp only [a, mul_pow, Finset.sum_mul]
      _ ≤ ∑ k ∈ S, NativeUnheatedRieszKernel.constant*|T k|^2 :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (kernel_square_sum k F) (sq_nonneg _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (square_sum_le T S) NativeUnheatedRieszKernel.constant_nonnegative
  have second : (∑ index ∈ S ×ˢ F, b index^2) ≤ ‖L‖^2*‖M‖^2 := by
    rw [Finset.sum_product, Finset.sum_comm]
    calc
      _ = ∑ p ∈ F, |L p|^2*(∑ k ∈ S, |M (k-p)|^2) := by
        simp only [b, mul_pow, Finset.mul_sum]
      _ ≤ ∑ p ∈ F, |L p|^2*‖M‖^2 :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (translated_square_sum M p S) (sq_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (square_sum_le L F) (sq_nonneg _)
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ F) a b
  have same : (∑ index ∈ S ×ˢ F, a index*b index) = ∑ index ∈ S ×ˢ F, term L M T index := by
    apply Finset.sum_congr rfl
    intro index _
    dsimp only [a, b, term]
    ring
  rw [same] at cauchy
  have paid := cauchy.trans (mul_le_mul first second
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity [NativeUnheatedRieszKernel.constant_nonnegative]))
  have positive : 0 ≤ Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by positivity
  have square := Real.sq_sqrt NativeUnheatedRieszKernel.constant_nonnegative
  rw [← square] at paid
  nlinarith only [paid, positive]

theorem finite_bound (L M T : E) (F : Finset (Wave × Wave)) :
    (∑ index ∈ F, term L M T index) ≤
      Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ := by
  classical
  apply le_trans _ (rectangle_bound L M T (F.image Prod.fst) (F.image Prod.snd))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro index inside
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst inside, Finset.mem_image_of_mem Prod.snd inside⟩
  · intro index _ _
    exact term_nonnegative L M T index

theorem summable (L M T : E) : Summable (term L M T) :=
  summable_of_sum_le (term_nonnegative L M T) (finite_bound L M T)

theorem bound (L M T : E) : (∑' index, term L M T index) ≤
    Real.sqrt NativeUnheatedRieszKernel.constant*‖L‖*‖M‖*‖T‖ :=
  (summable L M T).tsum_le_of_sum_le (finite_bound L M T)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeRieszKernel
