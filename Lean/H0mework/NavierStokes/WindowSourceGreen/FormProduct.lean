import H0mework.NavierStokes.UnheatedWriterTree.RieszPermutations

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowGreenProduct
open NativeUnheatedTreeRieszKernel (Wave E translated_square_sum)
open NativeUnheatedSchur (square_sum_le)
noncomputable section

structure Kernel where
  value : Wave → Wave → ℝ
  cap : ℝ
  cap_nonnegative : 0 ≤ cap
  nonnegative : ∀ k p, 0 ≤ value k p
  squares : ∀ k (F : Finset Wave), (∑ p ∈ F, value k p^2) ≤ cap

def term (kernel : Kernel) (L M T : E) (index : Wave × Wave) : ℝ :=
  kernel.value index.1 index.2*|L index.2| * |M (index.1-index.2)| * |T index.1|

theorem term_nonnegative (kernel : Kernel) (L M T : E) (index : Wave × Wave) : 0 ≤ term kernel L M T index := by
  unfold term
  positivity [kernel.nonnegative index.1 index.2]

theorem rectangle_bound (kernel : Kernel) (L M T : E) (S F : Finset Wave) :
    (∑ index ∈ S ×ˢ F, term kernel L M T index) ≤
      Real.sqrt kernel.cap*‖L‖*‖M‖*‖T‖ := by
  let a : Wave × Wave → ℝ := fun index => kernel.value index.1 index.2*|T index.1|
  let b : Wave × Wave → ℝ := fun index => |L index.2| *|M (index.1-index.2)|
  have first : (∑ index ∈ S ×ˢ F, a index^2) ≤ kernel.cap*‖T‖^2 := by
    rw [Finset.sum_product]
    calc
      _ = ∑ k ∈ S, (∑ p ∈ F, kernel.value k p^2)*|T k|^2 := by
        simp only [a, mul_pow, Finset.sum_mul]
      _ ≤ ∑ k ∈ S, kernel.cap*|T k|^2 :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (kernel.squares k F) (sq_nonneg _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (square_sum_le T S) kernel.cap_nonnegative
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
  have same : (∑ index ∈ S ×ˢ F, a index*b index) = ∑ index ∈ S ×ˢ F, term kernel L M T index := by
    apply Finset.sum_congr rfl
    intro index _
    dsimp only [a, b, term]
    ring
  rw [same] at cauchy
  have paid := cauchy.trans (mul_le_mul first second
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity [kernel.cap_nonnegative]))
  have positive : 0 ≤ Real.sqrt kernel.cap*‖L‖*‖M‖*‖T‖ := by positivity
  have square := Real.sq_sqrt kernel.cap_nonnegative
  rw [← square] at paid
  nlinarith only [paid, positive]

theorem finite_bound (kernel : Kernel) (L M T : E) (F : Finset (Wave × Wave)) :
    (∑ index ∈ F, term kernel L M T index) ≤
      Real.sqrt kernel.cap*‖L‖*‖M‖*‖T‖ := by
  classical
  apply le_trans _ (rectangle_bound kernel L M T (F.image Prod.fst) (F.image Prod.snd))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro index inside
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst inside, Finset.mem_image_of_mem Prod.snd inside⟩
  · intro index _ _
    exact term_nonnegative kernel L M T index

theorem summable (kernel : Kernel) (L M T : E) : Summable (term kernel L M T) :=
  summable_of_sum_le (term_nonnegative kernel L M T) (finite_bound kernel L M T)

theorem bound (kernel : Kernel) (L M T : E) : (∑' index, term kernel L M T index) ≤
    Real.sqrt kernel.cap*‖L‖*‖M‖*‖T‖ :=
  (summable kernel L M T).tsum_le_of_sum_le (finite_bound kernel L M T)

def row (kernel : Kernel) (L M : E) (k : Wave) : ℝ :=
  ∑' p, kernel.value k p*|L p| * |M (k-p)|

theorem row_nonnegative (kernel : Kernel) (L M : E) (k : Wave) : 0 ≤ row kernel L M k :=
  tsum_nonneg fun p => by positivity [kernel.nonnegative k p]

theorem row_summable (kernel : Kernel) (L M : E) (k : Wave) :
    Summable (fun p => kernel.value k p*|L p| * |M (k-p)|) := by
  have paid := (summable kernel L M (lp.single 2 k 1)).prod_factor k
  simpa only [term,lp.single_apply_self,abs_one,mul_one] using paid

theorem row_testing (kernel : Kernel) (L M T : E) :
    (∑' k, row kernel L M k*|T k|) ≤ Real.sqrt kernel.cap*‖L‖*‖M‖*‖T‖ := by
  have paid := (summable kernel L M T).tsum_prod
  simp only [term,tsum_mul_right] at paid
  change (∑' index, term kernel L M T index) = (∑' k, row kernel L M k*|T k|) at paid
  rw [← paid]
  exact bound kernel L M T

def test (kernel : Kernel) (L M : E) (F : Finset Wave) : E := ∑ k ∈ F, lp.single 2 k (row kernel L M k)

theorem test_apply (kernel : Kernel) (L M : E) (F : Finset Wave) (k : Wave) :
    test kernel L M F k = if k ∈ F then row kernel L M k else 0 := by
  classical
  simp only [test,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem test_square (kernel : Kernel) (L M : E) (F : Finset Wave) :
    ‖test kernel L M F‖^2 = ∑ k ∈ F, row kernel L M k^2 := by
  simpa only [test,ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (row kernel L M) F

theorem row_square_bound (kernel : Kernel) (L M : E) (F : Finset Wave) :
    (∑ k ∈ F, row kernel L M k^2) ≤ (Real.sqrt kernel.cap*‖L‖*‖M‖)^2 := by
  classical
  have paid := row_testing kernel L M (test kernel L M F)
  rw [tsum_eq_sum (s := F) (fun k outside => by simp only [test_apply,if_neg outside,abs_zero,mul_zero])] at paid
  simp only [test_apply] at paid
  have same : (∑ k ∈ F, row kernel L M k*|if k ∈ F then row kernel L M k else 0|) =
      ∑ k ∈ F, row kernel L M k^2 := by
    apply Finset.sum_congr rfl
    intro k inside
    rw [if_pos inside,abs_of_nonneg (row_nonnegative kernel L M k),pow_two]
  rw [same,← test_square] at paid
  have bounded : ‖test kernel L M F‖ ≤ Real.sqrt kernel.cap*‖L‖*‖M‖ := by
    rcases (norm_nonneg (test kernel L M F)).eq_or_lt with zero | positive
    · rw [← zero]
      positivity
    · apply (mul_le_mul_iff_left₀ positive).mp
      rw [pow_two] at paid
      exact paid.trans_eq (by ring)
  rw [← test_square]
  exact pow_le_pow_left₀ (norm_nonneg _) bounded 2

def value (kernel : Kernel) (L M : E) : E :=
  ⟨row kernel L M, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
    exact summable_of_sum_le (fun _ => sq_nonneg _) (row_square_bound kernel L M))⟩

theorem value_norm (kernel : Kernel) (L M : E) : ‖value kernel L M‖ ≤ Real.sqrt kernel.cap*‖L‖*‖M‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have same := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (value kernel L M)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at same
  rw [same]
  exact Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) (row_square_bound kernel L M)

abbrev ComplexSpace := lp (fun _ : Wave => ℂ) 2

def complexRow (K : Wave → Wave → ℂ) (L M : ComplexSpace) (k : Wave) : ℂ := ∑' p, K k p*L p*M (k-p)

theorem complex_bound (kernel : Kernel) (K : Wave → Wave → ℂ) (controlled : ∀ k p, ‖K k p‖ ≤ kernel.value k p)
    (L M : ComplexSpace) (k : Wave) : ‖complexRow K L M k‖ ≤ row kernel (lp.toNorm L) (lp.toNorm M) k := by
  have estimate (p : Wave) : ‖K k p*L p*M (k-p)‖ ≤ kernel.value k p*|lp.toNorm L p| * |lp.toNorm M (k-p)| := by
    simp only [norm_mul,lp.toNorm,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (controlled k p) (norm_nonneg _)) (norm_nonneg _)
  have paid := (row_summable kernel (lp.toNorm L) (lp.toNorm M) k).of_nonneg_of_le (fun _ => norm_nonneg _) estimate
  exact (norm_tsum_le_tsum_norm paid).trans (paid.tsum_le_tsum estimate (row_summable kernel (lp.toNorm L) (lp.toNorm M) k))

def complexValue (kernel : Kernel) (K : Wave → Wave → ℂ) (controlled : ∀ k p, ‖K k p‖ ≤ kernel.value k p)
    (L M : ComplexSpace) : ComplexSpace :=
  ⟨complexRow K L M, (lp.memℓp (value kernel (lp.toNorm L) (lp.toNorm M))).mono fun k =>
    complex_bound kernel K controlled L M k⟩

theorem complexValue_norm (kernel : Kernel) (K : Wave → Wave → ℂ) (controlled : ∀ k p, ‖K k p‖ ≤ kernel.value k p)
    (L M : ComplexSpace) : ‖complexValue kernel K controlled L M‖ ≤ Real.sqrt kernel.cap*‖L‖*‖M‖ := by
  have compared : ‖complexValue kernel K controlled L M‖ ≤ ‖value kernel (lp.toNorm L) (lp.toNorm M)‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro k
    change ‖complexRow K L M k‖ ≤ ‖row kernel (lp.toNorm L) (lp.toNorm M) k‖
    rw [Real.norm_of_nonneg (row_nonnegative kernel (lp.toNorm L) (lp.toNorm M) k)]
    exact complex_bound kernel K controlled L M k
  simpa only [lp.norm_toNorm] using compared.trans (value_norm kernel (lp.toNorm L) (lp.toNorm M))

end
end SaturationMonoid.NavierStokes.NativeWindowGreenProduct
