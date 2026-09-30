import H0mework.NavierStokes.WindowSourceGreen.FormTest
import H0mework.NavierStokes.WindowSourceSobolev.UniformTail

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowGreenCriticalForm
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeWindowGreenProduct NativeWindowGreenTestForm
open NativeWindowSobolevStress (quarter quarter_nonnegative quarter_sq)
open NativeCompleteStressCarrier (weight weight_pos)
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
noncomputable section

def kernel : Kernel where
  value k p := quarter k*Real.sqrt (weight p)*Real.sqrt (weight (k-p))
  cap := NativeUnheatedRieszKernel.constant
  cap_nonnegative := NativeUnheatedRieszKernel.constant_nonnegative
  nonnegative k p := by positivity [quarter_nonnegative k]
  squares k F := by
    simp only [mul_pow,quarter_sq,Real.sq_sqrt (weight_pos _).le,mul_assoc,← Finset.mul_sum]
    exact NativeUnheatedRieszKernel.finite_bound k F

theorem weight_neg (k : Wave) : weight (-k) = weight k := by
  simp only [weight,neg_eq_zero,integerWaveNormSq,Pi.neg_apply,Int.cast_neg,neg_sq]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def integrand (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) (index : Wave × Wave) : ℂ :=
  (quarter index.1 : ℂ)*c index.1*inner ℂ (decode T index.2) (A (decode T (index.2-index.1)))

theorem integrand_bound (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) (index : Wave × Wave) :
    ‖integrand c A T index‖ ≤ ‖A‖*term kernel (lp.toNorm T)
      (NativeUnheatedTreeRieszPermutations.flip (lp.toNorm T)) (lp.toNorm c) index := by
  have paid := (norm_inner_le_norm (𝕜 := ℂ) (decode T index.2) (A (decode T (index.2-index.1))))
    |>.trans (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _))
  rw [integrand,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (quarter_nonnegative _)]
  apply (mul_le_mul_of_nonneg_left paid (mul_nonneg (quarter_nonnegative _) (norm_nonneg _))).trans_eq
  have same : weight (index.2-index.1) = weight (index.1-index.2) := by
    rw [← neg_sub index.1 index.2,weight_neg]
  simp only [decode,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),term,kernel,
    lp.toNorm,NativeUnheatedTreeRieszPermutations.flip_apply,neg_sub,abs_of_nonneg (norm_nonneg _),same]
  ring

theorem form_summable (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) :
    Summable (fun index => ‖integrand c A T index‖) :=
  ((summable kernel (lp.toNorm T) (NativeUnheatedTreeRieszPermutations.flip (lp.toNorm T))
    (lp.toNorm c)).mul_left ‖A‖).of_nonneg_of_le (fun _ => norm_nonneg _) (integrand_bound c A T)

def form (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) : ℂ := ∑' index, integrand c A T index

theorem form_bound (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) :
    ‖form c A T‖ ≤ (‖A‖*Real.sqrt kernel.cap*‖c‖)*‖T‖^2 := by
  apply (norm_tsum_le_tsum_norm (form_summable c A T)).trans
  apply ((form_summable c A T).tsum_le_tsum (integrand_bound c A T)
    ((summable kernel (lp.toNorm T) (NativeUnheatedTreeRieszPermutations.flip (lp.toNorm T)) (lp.toNorm c)).mul_left ‖A‖)).trans
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (bound kernel (lp.toNorm T)
    (NativeUnheatedTreeRieszPermutations.flip (lp.toNorm T)) (lp.toNorm c)) (norm_nonneg A)).trans_eq (by
      rw [NativeUnheatedTreeRieszPermutations.flip_norm,lp.norm_toNorm,lp.norm_toNorm]; ring)

def low (F : Finset Wave) (c : ComplexSpace) : ComplexSpace := ∑ k ∈ F, lp.single 2 k ((quarter k : ℂ)*c k)
def high (F : Finset Wave) (c : ComplexSpace) : ComplexSpace :=
  ⟨fun k => if k ∈ F then 0 else c k, (lp.memℓp c).mono' fun k => by split_ifs <;> simp⟩

theorem low_read (F : Finset Wave) (c : ComplexSpace) (k : Wave) :
    low F c k = if k ∈ F then (quarter k : ℂ)*c k else 0 := by
  classical
  simp only [low,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem low_norm (F : Finset Wave) (c : ComplexSpace) : ‖low F c‖ ≤ (∑ k ∈ F, quarter k)*‖c‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  simp only [lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)),norm_mul,Complex.norm_real,Real.norm_of_nonneg (quarter_nonnegative _)]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) c k)
    (quarter_nonnegative k)

theorem form_split (F : Finset Wave) (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H) :
    form c A T = NativeWindowGreenTestForm.form (low F c) A T+form (high F c) A T := by
  rw [NativeWindowGreenTestForm.form,form,form,
    ← Summable.tsum_add (NativeWindowGreenTestForm.form_summable (low F c) A T).of_norm (form_summable (high F c) A T).of_norm]
  apply tsum_congr
  intro index
  simp only [integrand,NativeWindowGreenTestForm.integrand,low_read,high]
  split_ifs <;> simp

theorem split_absorption (F : Finset Wave) (c : ComplexSpace) (A : H →L[ℂ] H) (T : Test H)
    (epsilon : ℝ) (positive : 0 < epsilon)
    (small : ‖A‖*Real.sqrt kernel.cap*‖high F c‖ ≤ epsilon) :
    ‖form c A T‖ ≤ (2*epsilon)*gradient T+
      (2*epsilon+(‖A‖*Real.sqrt testKernel.cap*‖low F c‖)^8*epsilon⁻¹^7)*‖decode T‖^2 := by
  have highBound := (form_bound (high F c) A T).trans
    (mul_le_mul_of_nonneg_right small (sq_nonneg _))
  have highEnergy := mul_le_mul_of_nonneg_left (high_le_gradient_mass T) positive.le
  have lowBound := form_absorption (low F c) A T epsilon positive
  rw [form_split]
  have sumBound := norm_add_le (NativeWindowGreenTestForm.form (low F c) A T) (form (high F c) A T)
  apply (sumBound.trans (add_le_add lowBound (highBound.trans highEnergy))).trans_eq
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowGreenCriticalForm
