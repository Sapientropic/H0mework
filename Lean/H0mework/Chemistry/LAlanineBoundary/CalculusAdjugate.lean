import H0mework.Chemistry.LAlanineBoundary.CalculusCoordinates
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary.Calculus

noncomputable section
open scoped BigOperators

theorem adjugate_contDiff (f : Space → Space) (hf : ContDiff ℝ 2 f) (i j : Fin 3) :
    ContDiff ℝ 1 (fun p => (jacobian f p).adjugate i j) := by
  have h := jacobian_contDiff f hf
  simp only [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j
  · exact ((h 1 1).mul (h 2 2)).sub ((h 1 2).mul (h 2 1))
  · exact ((h 0 1).mul (h 2 2)).neg.add ((h 0 2).mul (h 2 1))
  · exact ((h 0 1).mul (h 1 2)).sub ((h 0 2).mul (h 1 1))
  · exact ((h 1 0).mul (h 2 2)).neg.add ((h 1 2).mul (h 2 0))
  · exact ((h 0 0).mul (h 2 2)).sub ((h 0 2).mul (h 2 0))
  · exact ((h 0 0).mul (h 1 2)).neg.add ((h 0 2).mul (h 1 0))
  · exact ((h 1 0).mul (h 2 1)).sub ((h 1 1).mul (h 2 0))
  · exact ((h 0 0).mul (h 2 1)).neg.add ((h 0 1).mul (h 2 0))
  · exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))

/-- Column divergence of the actual cofactor field vanishes by equality of mixed derivatives. -/
theorem adjugate_divergence (f : Space → Space) (hf : ContDiff ℝ 2 f) (p : Space) (k : Fin 3) :
    (∑ i : Fin 3, dcoord (fun x => (jacobian f x).adjugate i k) i p) = 0 := by
  have hj (a b : Fin 3) : Differentiable ℝ (fun x => jacobian f x a b) :=
    (jacobian_contDiff f hf a b).differentiable (by norm_num)
  have h01 (a : Fin 3) := jacobian_mixed f hf p a 1 0
  have h02 (a : Fin 3) := jacobian_mixed f hf p a 2 0
  have h12 (a : Fin 3) := jacobian_mixed f hf p a 2 1
  fin_cases k <;> simp only [Fin.sum_univ_three, Matrix.adjugate_fin_three]
  · change dcoord (fun x => jacobian f x 1 1 * jacobian f x 2 2 - jacobian f x 1 2 * jacobian f x 2 1) 0 p +
      dcoord (fun x => -(jacobian f x 1 0 * jacobian f x 2 2) + jacobian f x 1 2 * jacobian f x 2 0) 1 p +
      dcoord (fun x => jacobian f x 1 0 * jacobian f x 2 1 - jacobian f x 1 1 * jacobian f x 2 0) 2 p = 0
    simp (discharger := fun_prop) only [partial_add, partial_sub, partial_mul, partial_neg, h01, h02, h12]
    ring
  · change dcoord (fun x => -(jacobian f x 0 1 * jacobian f x 2 2) + jacobian f x 0 2 * jacobian f x 2 1) 0 p +
      dcoord (fun x => jacobian f x 0 0 * jacobian f x 2 2 - jacobian f x 0 2 * jacobian f x 2 0) 1 p +
      dcoord (fun x => -(jacobian f x 0 0 * jacobian f x 2 1) + jacobian f x 0 1 * jacobian f x 2 0) 2 p = 0
    simp (discharger := fun_prop) only [partial_add, partial_sub, partial_mul, partial_neg, h01, h02, h12]
    ring
  · change dcoord (fun x => jacobian f x 0 1 * jacobian f x 1 2 - jacobian f x 0 2 * jacobian f x 1 1) 0 p +
      dcoord (fun x => -(jacobian f x 0 0 * jacobian f x 1 2) + jacobian f x 0 2 * jacobian f x 1 0) 1 p +
      dcoord (fun x => jacobian f x 0 0 * jacobian f x 1 1 - jacobian f x 0 1 * jacobian f x 1 0) 2 p = 0
    simp (discharger := fun_prop) only [partial_add, partial_sub, partial_mul, partial_neg, h01, h02, h12]
    ring

theorem adjugate_trace_contraction (A B : Matrix3) :
    (∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, A.adjugate i k * B k j * A j i) =
      A.det * ∑ i : Fin 3, B i i := by
  calc
    _ = (A.adjugate * B * A).trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm (f := fun (k j : Fin 3) => A.adjugate i k * B k j * A j i)
    _ = (A * A.adjugate * B).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by
      rw [Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
      rfl

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary.Calculus
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
