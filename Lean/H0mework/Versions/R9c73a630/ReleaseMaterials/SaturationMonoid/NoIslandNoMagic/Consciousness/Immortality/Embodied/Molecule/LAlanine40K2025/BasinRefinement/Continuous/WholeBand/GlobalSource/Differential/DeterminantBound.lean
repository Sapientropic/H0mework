import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel SourceFiniteData ContinuousGradient
open _root_.LAlanineTrueFlowDifferential
noncomputable section

private theorem det_three_bound (M : Matrix (Fin 3) (Fin 3) ℝ) (bound : ∀ i j, |M i j| ≤ 2) :
    |M.det| ≤ 48 := by
  have triple (a b c d e f : Fin 3) : |M a b*M c d*M e f| ≤ 8 := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ (2 : ℝ)*2*2 := mul_le_mul
        (mul_le_mul (bound a b) (bound c d) (abs_nonneg _) (by norm_num))
        (bound e f) (abs_nonneg _) (by norm_num)
      _ = 8 := by norm_num
  have h0 := abs_le.mp (triple 0 0 1 1 2 2)
  have h1 := abs_le.mp (triple 0 0 1 2 2 1)
  have h2 := abs_le.mp (triple 0 1 1 0 2 2)
  have h3 := abs_le.mp (triple 0 1 1 2 2 0)
  have h4 := abs_le.mp (triple 0 2 1 0 2 1)
  have h5 := abs_le.mp (triple 0 2 1 1 2 0)
  rw [Matrix.det_fin_three]
  apply abs_le.mpr
  constructor <;> linarith

theorem response_determinant_bound (x : Point) (t : Time) : |(responseMatrix x t).det| ≤ 48 :=
  det_three_bound _ (responseMatrix_entry_bound x t)

theorem laplacian_step_bound (x : Point) : |spatialStep*laplacian sourceTerms densityMatrix x| ≤ 3 := by
  rw [← TrueFlowConservation.sourceHessian_trace]
  simp only [Matrix.trace,Matrix.diag,TrueFlowConservation.hessianMatrix,Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin 3, |spatialStep * sourceHessian x i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 3, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have entry := (norm_le_pi_norm (derivative x (Pi.single i 1)) i).trans
        ((derivative x).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (derivative_bound x) (norm_nonneg _)))
      simpa only [derivative,_root_.smul_apply,Pi.smul_apply,smul_eq_mul,sourceHessianLinear_apply,
        Pi.single_apply,mul_ite,Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_one,mul_zero,
        Real.norm_eq_abs,Pi.norm_single,norm_one] using entry
    _ = 3 := by norm_num

theorem determinant_rate_bound (x : Point) (t : Time) :
    |spatialStep*laplacian sourceTerms densityMatrix (actualPath x t)*(responseMatrix x t).det| ≤ 144 := by
  rw [abs_mul]
  exact (mul_le_mul (laplacian_step_bound _) (response_determinant_bound x t) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
