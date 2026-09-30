import H0mework.NavierStokes.UnheatedWriterTree.HeatSpace

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportProduct
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedSexticLatticePower
open NativeUnheatedTreeRieszPermutations
noncomputable section

abbrev Z := NativeUnheatedTreeHeatSpace.ComplexSpace

def kernel (p q : Wave) : ℝ := density 2 (p+q)*density 1 q

theorem kernel_nonnegative (p q : Wave) : 0 ≤ kernel p q := by
  unfold kernel
  positivity [density_positive 2 (p+q),density_positive 1 q]

theorem radical_sub (p k : Wave) : radical (k-p) ≤ 2*max (radical p) (radical k) := by
  have geometry := NativeUnheatedTreeHeatKernel.mass_add k (-p)
  have negmass : mass (-p) = mass p := by
    simp only [mass, ThreeDimensionalVorticityCoefficientRawSourceCore.integerWaveNormSq,
      Pi.neg_apply, Int.cast_neg, neg_sq]
  rw [negmass, ← sub_eq_add_neg] at geometry
  have a := pow_le_pow_left₀ (radical_positive p).le (le_max_left (radical p) (radical k)) 4
  have b := pow_le_pow_left₀ (radical_positive k).le (le_max_right (radical p) (radical k)) 4
  rw [radical_fourth] at a b
  have max0 : 0 ≤ max (radical p) (radical k) := (radical_positive p).le.trans (le_max_left _ _)
  apply (pow_le_pow_iff_left₀ (radical_positive (k-p)).le (mul_nonneg (by norm_num) max0) (by decide : (4 : ℕ) ≠ 0)).mp
  rw [radical_fourth, mul_pow]
  norm_num
  nlinarith only [geometry,a,b,pow_nonneg max0 4]

theorem kernel_bound (p q : Wave) : kernel p q ≤
    2*(radical p*density 2 q*density 2 (p+q)+radical (p+q)*density 2 p*density 2 q) := by
  have shape := radical_sub p (p+q)
  rw [add_sub_cancel_left] at shape
  have numerator : radical p^2*radical q ≤ 2*(radical p^3+radical (p+q)^3) := by
    rcases le_total (radical p) (radical (p+q)) with order | order
    · rw [max_eq_right order] at shape
      have paid := mul_le_mul (pow_le_pow_left₀ (radical_positive p).le order 2) shape
        (radical_positive q).le (sq_nonneg _)
      nlinarith only [paid,pow_nonneg (radical_positive p).le 3]
    · rw [max_eq_left order] at shape
      have paid := mul_le_mul_of_nonneg_left shape (sq_nonneg (radical p))
      nlinarith only [paid,pow_nonneg (radical_positive (p+q)).le 3]
  unfold kernel density
  apply (mul_le_mul_iff_right₀ (show 0 < radical p^2*radical q^2*radical (p+q)^2 by positivity [radical_positive p,radical_positive q,radical_positive (p+q)])).mp
  convert! numerator using 1 <;> field_simp [(radical_positive p).ne',(radical_positive q).ne',(radical_positive (p+q)).ne']

def term (L M T : E) (index : Wave × Wave) : ℝ :=
  kernel index.1 index.2*|L index.1| * |M index.2| * |T (index.1+index.2)|

theorem term_nonnegative (L M T : E) (index : Wave × Wave) : 0 ≤ term L M T index := by
  unfold term kernel
  positivity [density_positive 2 (index.1+index.2),density_positive 1 index.2]

theorem term_bound (L M T : E) (index : Wave × Wave) : term L M T index ≤
    2*(firstTerm L M T index+outputTerm L M T index) := by
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (kernel_bound index.1 index.2) (abs_nonneg (L index.1))) (abs_nonneg (M index.2))) (abs_nonneg (T (index.1+index.2)))).trans_eq
      (by unfold firstTerm outputTerm; ring)

theorem summable (L M T : E) : Summable (term L M T) :=
  (((first_summable L M T).add (output_summable L M T)).mul_left 2).of_nonneg_of_le
    (term_nonnegative L M T) (term_bound L M T)

def cap : ℝ := 4*Real.sqrt NativeUnheatedRieszKernel.constant

theorem cap_nonnegative : 0 ≤ cap := by unfold cap; positivity

theorem bound (L M T : E) : (∑' index, term L M T index) ≤ cap*‖L‖*‖M‖*‖T‖ := by
  have paid := (summable L M T).tsum_le_tsum (term_bound L M T)
    (((first_summable L M T).add (output_summable L M T)).mul_left 2)
  rw [tsum_mul_left,(first_summable L M T).tsum_add (output_summable L M T)] at paid
  exact paid.trans ((mul_le_mul_of_nonneg_left (add_le_add (first_bound L M T) (output_bound L M T))
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by unfold cap; ring))


def row (L M : E) (k : Wave) : ℝ := ∑' p, kernel p (k-p)*|L p| * |M (k-p)|

theorem row_nonnegative (L M : E) (k : Wave) : 0 ≤ row L M k := by
  apply tsum_nonneg
  intro p
  unfold kernel
  positivity [density_positive 2 (p+(k-p)),density_positive 1 (k-p)]

theorem pair_recognition (L M T : E) (index : Wave × Wave) :
    kernel index.2 (index.1-index.2)*|L index.2| * |M (index.1-index.2)| * |T index.1| =
      term L M T (outputEquiv.symm index) := by
  simp only [term,outputEquiv,Equiv.coe_fn_symm_mk,add_sub_cancel]

theorem pair_summable (L M T : E) : Summable (fun index : Wave × Wave =>
    kernel index.2 (index.1-index.2)*|L index.2| * |M (index.1-index.2)| * |T index.1|) := by
  simp_rw [pair_recognition]
  exact outputEquiv.symm.summable_iff.mpr (summable L M T)

theorem row_summable (L M : E) (k : Wave) :
    Summable (fun p => kernel p (k-p)*|L p| * |M (k-p)|) := by
  simpa only [lp.single_apply_self,abs_one,mul_one] using
    (pair_summable L M (lp.single 2 k 1)).prod_factor k

theorem testing_bound (L M T : E) : (∑' k, row L M k*|T k|) ≤ cap*‖L‖*‖M‖*‖T‖ := by
  have same := (pair_summable L M T).tsum_prod
  simp only [tsum_mul_right] at same
  change _ = ∑' k,row L M k*|T k| at same
  rw [← same]
  simp_rw [pair_recognition]
  rw [outputEquiv.symm.tsum_eq]
  exact bound L M T

def test (L M : E) (F : Finset Wave) : E := ∑ k ∈ F, lp.single 2 k (row L M k)

theorem test_apply (L M : E) (F : Finset Wave) (k : Wave) : test L M F k = if k∈F then row L M k else 0 := by
  classical
  simp only [test,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem test_square (L M : E) (F : Finset Wave) : ‖test L M F‖^2 = ∑ k∈F, row L M k^2 := by
  simpa only [test,ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (row L M) F

theorem finite_bound (L M : E) (F : Finset Wave) : (∑ k∈F, row L M k^2) ≤ (cap*‖L‖*‖M‖)^2 := by
  classical
  have identity : (∑' k, row L M k*|test L M F k|) = ∑ k∈F, row L M k^2 := by
    rw [tsum_eq_sum (s := F) (fun k outside => by simp only [test_apply,if_neg outside,abs_zero,mul_zero])]
    apply Finset.sum_congr rfl
    intro k inside
    rw [test_apply,if_pos inside,abs_of_nonneg (row_nonnegative L M k),pow_two]
  have paid := testing_bound L M (test L M F)
  rw [identity,← test_square] at paid
  have scalar : ‖test L M F‖ ≤ cap*‖L‖*‖M‖ := by
    rcases (norm_nonneg (test L M F)).eq_or_lt with zero | positive
    · rw [← zero]; positivity [cap_nonnegative]
    · apply (mul_le_mul_iff_left₀ positive).mp
      rw [pow_two] at paid
      exact paid.trans_eq (by ring)
  rw [← test_square]
  exact pow_le_pow_left₀ (norm_nonneg _) scalar 2

def value (L M : E) : E := ⟨row L M,memℓp_gen (by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    summable_of_sum_le (fun k => sq_nonneg (row L M k)) (finite_bound L M))⟩

theorem value_norm (L M : E) : ‖value L M‖ ≤ cap*‖L‖*‖M‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [cap_nonnegative])).mp
  have actual := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (value L M)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at actual
  rw [actual]
  exact (summable_of_sum_le (fun k => sq_nonneg (row L M k)) (finite_bound L M)).tsum_le_of_sum_le (finite_bound L M)

def complexTerm (L M : Z) (k p : Wave) : ℂ := (kernel p (k-p) : ℂ)*L p*M (k-p)

theorem complex_summable (L M : Z) (k : Wave) : Summable (fun p => ‖complexTerm L M k p‖) := by
  simpa only [complexTerm,norm_mul,Complex.norm_real,Real.norm_of_nonneg (kernel_nonnegative _ _),lp.toNorm,abs_of_nonneg (norm_nonneg _)] using
      row_summable (lp.toNorm L) (lp.toNorm M) k

theorem complex_row_bound (L M : Z) (k : Wave) : ‖∑' p, complexTerm L M k p‖ ≤ row (lp.toNorm L) (lp.toNorm M) k := by
  have paid := norm_tsum_le_tsum_norm (complex_summable L M k)
  simpa only [complexTerm,norm_mul,Complex.norm_real,Real.norm_of_nonneg (kernel_nonnegative _ _),row,lp.toNorm,abs_of_nonneg (norm_nonneg _)] using paid

def product (L M : Z) : Z := ⟨fun k => ∑' p,complexTerm L M k p,
  (lp.memℓp (value (lp.toNorm L) (lp.toNorm M))).mono (complex_row_bound L M)⟩

theorem product_row (L M : Z) (k : Wave) : product L M k =
    (density 2 k : ℂ)*(∑' p,L p*((density 1 (k-p) : ℂ)*M (k-p))) := by
  change (∑' p,complexTerm L M k p) = _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [complexTerm,kernel,add_sub_cancel,Complex.ofReal_mul]
  ring

theorem product_bound (L M : Z) : ‖product L M‖ ≤ cap*‖L‖*‖M‖ := by
  have compared : ‖product L M‖ ≤ ‖value (lp.toNorm L) (lp.toNorm M)‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro k
    change ‖∑' p,complexTerm L M k p‖ ≤ ‖row (lp.toNorm L) (lp.toNorm M) k‖
    rw [Real.norm_of_nonneg (row_nonnegative _ _ k)]
    exact complex_row_bound L M k
  simpa only [lp.norm_toNorm] using compared.trans (value_norm (lp.toNorm L) (lp.toNorm M))


theorem product_finite_row (L M : Z) (F : Finset Wave) (supported : ∀ p∉F,L p=0) (k : Wave) :
    product L M k = (density 2 k : ℂ)*(∑ p∈F,L p*((density 1 (k-p) : ℂ)*M (k-p))) := by
  rw [product_row,tsum_eq_sum (s := F) (fun p outside => by rw [supported p outside,zero_mul])]

theorem product_supported (L M : Z) (F G : Finset Wave)
    (left : ∀ p∉F,L p=0) (right : ∀ q∉G,M q=0) (k : Wave) (outside : k∉F+G) : product L M k=0 := by
  classical
  rw [product_finite_row L M F left]
  have zero (p : Wave) (inside : p∈F) : M (k-p)=0 := right _ (fun member => outside
    (Finset.mem_add.mpr ⟨p,inside,k-p,member,by abel⟩))
  suffices same : (∑ p∈F,L p*((density 1 (k-p) : ℂ)*M (k-p)))=0 by rw [same,mul_zero]
  exact Finset.sum_eq_zero fun p inside => by rw [zero p inside,mul_zero,mul_zero]


theorem product_continuous {X : Type*} [TopologicalSpace X] {L M : X → Z} (F G : Finset Wave)
    (first : Continuous L) (last : Continuous M) (left : ∀ x p,p∉F → L x p=0)
    (right : ∀ x q,q∉G → M x q=0) : Continuous (fun x => product (L x) (M x)) := by
  classical
  have coordinate (k : Wave) : Continuous (fun x => product (L x) (M x) k) := by
    simp_rw [product_finite_row _ _ F (left _)]
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro p _
    exact ((lp.evalCLM ℂ (fun _ : Wave => ℂ) 2 p).continuous.comp first).mul
      (((lp.evalCLM ℂ (fun _ : Wave => ℂ) 2 (k-p)).continuous.comp last).const_mul _)
  have same : (fun x => product (L x) (M x)) = fun x => ∑ k∈F+G,lp.single 2 k (product (L x) (M x) k) := by
    funext x
    apply lp.ext
    funext k
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
    split_ifs with inside
    · rfl
    · exact product_supported (L x) (M x) F G (left x) (right x) k inside
  rw [same]
  exact continuous_finsetSum _ fun k _ =>
    (lp.singleContinuousLinearMap ℂ (fun _ : Wave => ℂ) 2 k).continuous.comp (coordinate k)

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportProduct
