import H0mework.NavierStokes.UnheatedWriterTree.HeatConvolution

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatSpace
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedTreeHeatConvolution
noncomputable section

def test (a b : ℝ) (L M : E) (F : Finset Wave) : E :=
  ∑ k ∈ F, lp.single 2 k (row a b L M k)

theorem test_apply (a b : ℝ) (L M : E) (F : Finset Wave) (k : Wave) :
    test a b L M F k = if k ∈ F then row a b L M k else 0 := by
  classical
  simp only [test, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

theorem test_square (a b : ℝ) (L M : E) (F : Finset Wave) :
    ‖test a b L M F‖^2 = ∑ k ∈ F, row a b L M k^2 := by
  simpa only [test, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (row a b L M) F

theorem test_identity (a b : ℝ) (L M : E) (F : Finset Wave) :
    (∑' k, row a b L M k*|test a b L M F k|) = ∑ k ∈ F, row a b L M k^2 := by
  classical
  rw [tsum_eq_sum (s := F) (fun k outside => by simp only [test_apply, if_neg outside, abs_zero, mul_zero])]
  apply Finset.sum_congr rfl
  intro k inside
  rw [test_apply, if_pos inside, abs_of_nonneg (row_nonnegative a b L M k), pow_two]

theorem finite_square_bound (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M : E) (F : Finset Wave) :
    (∑ k ∈ F, row a b L M k^2) ≤ (cap*‖L‖*‖M‖)^2 := by
  have paid := testing_bound a b first last total L M (test a b L M F)
  rw [test_identity, ← test_square] at paid
  have scalar : ‖test a b L M F‖ ≤ cap*‖L‖*‖M‖ := by
    rcases (norm_nonneg (test a b L M F)).eq_or_lt with zero | positive
    · rw [← zero]
      positivity [cap_nonnegative]
    · apply (mul_le_mul_iff_left₀ positive).mp
      rw [pow_two] at paid
      exact paid.trans_eq (by ring)
  rw [← test_square]
  exact pow_le_pow_left₀ (norm_nonneg _) scalar 2

theorem square_summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M : E) : Summable (fun k => row a b L M k^2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (finite_square_bound a b first last total L M)

theorem square_bound (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M : E) : (∑' k, row a b L M k^2) ≤ (cap*‖L‖*‖M‖)^2 :=
  (square_summable a b first last total L M).tsum_le_of_sum_le (finite_square_bound a b first last total L M)

def value (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b) (L M : E) : E :=
  ⟨row a b L M, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      square_summable a b first last total L M)⟩

theorem value_apply (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M : E) (k : Wave) : value a b first last total L M k =
      ∑' p, NativeUnheatedTreeHeatKernel.kernel a b p (k-p)*|L p| * |M (k-p)| := rfl

theorem value_norm (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (L M : E) : ‖value a b first last total L M‖ ≤ cap*‖L‖*‖M‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [cap_nonnegative])).mp
  have actual := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (value a b first last total L M)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at actual
  rw [actual]
  exact square_bound a b first last total L M

abbrev ComplexSpace := lp (fun _ : Wave => ℂ) 2

def complexTerm (kernel : Wave → Wave → ℂ) (L M : ComplexSpace) (k p : Wave) : ℂ :=
  kernel p (k-p)*L p*M (k-p)

def complexRow (kernel : Wave → Wave → ℂ) (L M : ComplexSpace) (k : Wave) : ℂ :=
  ∑' p, complexTerm kernel L M k p

theorem complex_term_bound (a b : ℝ) (kernel : Wave → Wave → ℂ)
    (controlled : ∀ p q, ‖kernel p q‖ ≤ NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) (k p : Wave) : ‖complexTerm kernel L M k p‖ ≤ term a b (lp.toNorm L) (lp.toNorm M) k p := by
  simp only [complexTerm, norm_mul, term, lp.toNorm, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (controlled p (k-p)) (norm_nonneg _)) (norm_nonneg _)

theorem complex_absolute_summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (kernel : Wave → Wave → ℂ) (controlled : ∀ p q, ‖kernel p q‖ ≤ NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) (k : Wave) : Summable (fun p => ‖complexTerm kernel L M k p‖) :=
  (row_summable a b first last total (lp.toNorm L) (lp.toNorm M) k).of_nonneg_of_le
    (fun _ => norm_nonneg _) (complex_term_bound a b kernel controlled L M k)

theorem complex_row_bound (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (kernel : Wave → Wave → ℂ) (controlled : ∀ p q, ‖kernel p q‖ ≤ NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) (k : Wave) : ‖complexRow kernel L M k‖ ≤ row a b (lp.toNorm L) (lp.toNorm M) k := by
  apply (norm_tsum_le_tsum_norm (complex_absolute_summable a b first last total kernel controlled L M k)).trans
  exact (complex_absolute_summable a b first last total kernel controlled L M k).tsum_le_tsum
    (complex_term_bound a b kernel controlled L M k) (row_summable a b first last total (lp.toNorm L) (lp.toNorm M) k)

def complexValue (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (kernel : Wave → Wave → ℂ) (controlled : ∀ p q, ‖kernel p q‖ ≤ NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) : ComplexSpace :=
  ⟨complexRow kernel L M, (lp.memℓp (value a b first last total (lp.toNorm L) (lp.toNorm M))).mono
    (complex_row_bound a b first last total kernel controlled L M)⟩

theorem complexValue_apply (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (kernel : Wave → Wave → ℂ) (controlled : ∀ p q, ‖kernel p q‖ ≤ NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) (k : Wave) : complexValue a b first last total kernel controlled L M k =
      ∑' p, kernel p (k-p)*L p*M (k-p) := rfl

theorem complexValue_norm (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (kernel : Wave → Wave → ℂ) (controlled : ∀ p q, ‖kernel p q‖ ≤ NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) : ‖complexValue a b first last total kernel controlled L M‖ ≤ cap*‖L‖*‖M‖ := by
  have compared : ‖complexValue a b first last total kernel controlled L M‖ ≤
      ‖value a b first last total (lp.toNorm L) (lp.toNorm M)‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro k
    change ‖complexRow kernel L M k‖ ≤ ‖row a b (lp.toNorm L) (lp.toNorm M) k‖
    rw [Real.norm_of_nonneg (row_nonnegative a b (lp.toNorm L) (lp.toNorm M) k)]
    exact complex_row_bound a b first last total kernel controlled L M k
  simpa only [lp.norm_toNorm] using compared.trans (value_norm a b first last total (lp.toNorm L) (lp.toNorm M))

theorem normalized_kernel_bound (a b factor : ℝ) (positive : 0 < factor) (kernel : Wave → Wave → ℂ)
    (controlled : ∀ p q, ‖kernel p q‖ ≤ factor*NativeUnheatedTreeHeatKernel.kernel a b p q) (p q : Wave) :
    ‖factor⁻¹ • kernel p q‖ ≤ NativeUnheatedTreeHeatKernel.kernel a b p q := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
  exact (mul_le_mul_of_nonneg_left (controlled p q) (inv_nonneg.mpr positive.le)).trans_eq (by
    rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul])

theorem scaled_absolute_summable (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (factor : ℝ) (kernel : Wave → Wave → ℂ)
    (controlled : ∀ p q, ‖kernel p q‖ ≤ factor*NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) (k : Wave) : Summable (fun p => ‖complexTerm kernel L M k p‖) := by
  apply ((row_summable a b first last total (lp.toNorm L) (lp.toNorm M) k).mul_left factor).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  simp only [complexTerm, norm_mul, term, lp.toNorm, abs_of_nonneg (norm_nonneg _)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (controlled p (k-p)) (norm_nonneg _))
    (norm_nonneg _)).trans_eq (by ring)

def scaledComplexValue (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (factor : ℝ) (positive : 0 < factor) (kernel : Wave → Wave → ℂ)
    (controlled : ∀ p q, ‖kernel p q‖ ≤ factor*NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) : ComplexSpace :=
  factor • complexValue a b first last total (fun p q => factor⁻¹ • kernel p q)
    (normalized_kernel_bound a b factor positive kernel controlled) L M

theorem scaledComplexValue_apply (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (factor : ℝ) (positive : 0 < factor) (kernel : Wave → Wave → ℂ)
    (controlled : ∀ p q, ‖kernel p q‖ ≤ factor*NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) (k : Wave) : scaledComplexValue a b first last total factor positive kernel controlled L M k =
      ∑' p, kernel p (k-p)*L p*M (k-p) := by
  change factor • (∑' p, (factor⁻¹ • kernel p (k-p))*L p*M (k-p)) = _
  rw [← tsum_const_smul'' factor]
  apply tsum_congr
  intro p
  rw [← smul_mul_assoc, ← smul_mul_assoc, smul_inv_smul₀ positive.ne']

theorem scaledComplexValue_norm (a b : ℝ) (first : a ≤ 1/2) (last : b ≤ 1/2) (total : -1 ≤ a+b)
    (factor : ℝ) (positive : 0 < factor) (kernel : Wave → Wave → ℂ)
    (controlled : ∀ p q, ‖kernel p q‖ ≤ factor*NativeUnheatedTreeHeatKernel.kernel a b p q)
    (L M : ComplexSpace) : ‖scaledComplexValue a b first last total factor positive kernel controlled L M‖ ≤
      factor*cap*‖L‖*‖M‖ := by
  rw [scaledComplexValue, norm_smul, Real.norm_of_nonneg positive.le]
  exact (mul_le_mul_of_nonneg_left (complexValue_norm a b first last total
    (fun p q => factor⁻¹ • kernel p q) (normalized_kernel_bound a b factor positive kernel controlled) L M)
    positive.le).trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeHeatSpace
