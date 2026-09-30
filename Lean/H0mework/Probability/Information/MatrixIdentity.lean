import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceBinaryMatrix

open scoped ComplexOrder
noncomputable section

variable {Index : Type*} [Fintype Index]

def mixture (weight : Index → ℝ) (state : Index → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := ∑ index, weight index • state index

theorem mixture_entry (weight : Index → ℝ) (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (row column : Fin 2) :
    mixture weight state row column = ∑ index, (weight index : ℂ) * state index row column := by
  simp [mixture, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]

theorem mixture_real (weight : Index → ℝ) (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (row column : Fin 2) :
    (mixture weight state row column).re = ∑ index, weight index * (state index row column).re := by
  simp [mixture_entry, Complex.mul_re]

theorem mixture_positive (weight : Index → ℝ) (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (nonnegative : ∀ index, 0 ≤ weight index) (positive : ∀ index, (state index).PosSemidef) :
    (mixture weight state).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ fun index _ =>
    (positive index).smul (nonnegative index)

theorem mixture_trace (weight : Index → ℝ) (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (total : ∑ index, weight index = 1) (normalized : ∀ index, (state index).trace = 1) :
    (mixture weight state).trace = 1 := by
  simp only [mixture, Matrix.trace_sum, Matrix.trace_smul, normalized, Complex.real_smul, mul_one]
  exact_mod_cast total

private theorem diagonal_imaginary (state : Matrix (Fin 2) (Fin 2) ℂ)
    (hermitian : state.IsHermitian) (index : Fin 2) : (state index index).im = 0 := by
  have equation := congrArg Complex.im (hermitian.apply index index)
  simp only [Complex.star_def, Complex.conj_im] at equation
  linarith

theorem determinant_scalar (state : Matrix (Fin 2) (Fin 2) ℂ)
    (hermitian : state.IsHermitian) (normalized : state.trace = 1) :
    state.det.re = (state 0 0).re * (1 - (state 0 0).re) - ‖state 0 1‖ ^ 2 := by
  have traceReal := congrArg Complex.re normalized
  simp only [Matrix.trace_fin_two, Complex.add_re, Complex.one_re] at traceReal
  rw [Matrix.det_fin_two, ← hermitian.apply 1 0, Complex.sub_re, Complex.mul_re,
    diagonal_imaginary state hermitian 0, zero_mul, sub_zero, Complex.mul_re]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  have second : (state 1 1).re = 1 - (state 0 0).re := by linarith
  rw [second]
  ring

private theorem real_centered (weight value : Index → ℝ) (total : ∑ index, weight index = 1) :
    (∑ index, weight index * (value index - ∑ other, weight other * value other) ^ 2) =
      (∑ index, weight index * value index ^ 2) - (∑ index, weight index * value index) ^ 2 := by
  let mean := ∑ index, weight index * value index
  change (∑ index, weight index * (value index - mean) ^ 2) = _
  calc
    _ = ∑ index, (weight index * value index ^ 2 -
        2 * (weight index * value index) * mean + weight index * mean ^ 2) := by
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, ← Finset.sum_mul, total]
      dsimp [mean]
      ring

private theorem complex_centered (weight : Index → ℝ) (value : Index → ℂ)
    (total : ∑ index, weight index = 1) :
    (∑ index, weight index * ‖value index - ∑ other, (weight other : ℂ) * value other‖ ^ 2) =
      (∑ index, weight index * ‖value index‖ ^ 2) -
        ‖∑ index, (weight index : ℂ) * value index‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  simp only [← sq, mul_add, Finset.sum_add_distrib]
  rw [real_centered weight (fun index => (value index).re) total,
    real_centered weight (fun index => (value index).im) total]
  ring

theorem determinant_decomposition (weight : Index → ℝ)
    (state : Index → Matrix (Fin 2) (Fin 2) ℂ)
    (nonnegative : ∀ index, 0 ≤ weight index) (total : ∑ index, weight index = 1)
    (positive : ∀ index, (state index).PosSemidef)
    (normalized : ∀ index, (state index).trace = 1) :
    (mixture weight state).det.re =
      (∑ index, weight index * ((state index 0 0).re - (mixture weight state 0 0).re) ^ 2) +
      (∑ index, weight index * (state index).det.re) +
      ∑ index, weight index * ‖state index 0 1 - mixture weight state 0 1‖ ^ 2 := by
  rw [determinant_scalar _ (mixture_positive weight state nonnegative positive).isHermitian
    (mixture_trace weight state total normalized)]
  simp_rw [determinant_scalar _ (positive _).isHermitian (normalized _)]
  rw [mixture_real, mixture_entry,
    real_centered weight (fun index => (state index 0 0).re) total,
    complex_centered weight (fun index => state index 0 1) total]
  have sumDet : (∑ index, weight index *
        ((state index 0 0).re * (1 - (state index 0 0).re) - ‖state index 0 1‖ ^ 2)) =
      (∑ index, weight index * (state index 0 0).re) -
        (∑ index, weight index * (state index 0 0).re ^ 2) -
        ∑ index, weight index * ‖state index 0 1‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [sumDet]
  ring

end
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceBinaryMatrix
