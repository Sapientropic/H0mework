import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Norm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem integer_ratio_norm (a d : Int) (positive : 0 < d) (bound : |a| ≤ d) :
    ‖(a : ℂ)/((d : ℂ)*10^24)‖ ≤ (1/10^24 : ℝ) := by
  have dp : (0 : ℝ) < d := by exact_mod_cast positive
  have b : |(a : ℝ)| ≤ (d : ℝ) := by exact_mod_cast bound
  rw [norm_div,norm_mul,Complex.norm_intCast]
  norm_num
  rw [abs_of_pos dp,div_le_iff₀ (by positivity)]
  nlinarith

theorem integer_matrix_residual (A B C : Matrix Basis Basis Int) (p d : Int)
    (positive : 0 < d) (bound : ∀ i j, |p*(A*B) i j-d*C i j| ≤ d) :
    ‖(1/10^24 : ℂ) • Cast.complexMatrix C-
      ((p : ℂ)/(d : ℂ)) • (Cast.complexMatrix A*((1/10^24 : ℂ) • Cast.complexMatrix B))‖ ≤ (1/10^22 : ℝ) := by
  have dn : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
  have entry (i j : Basis) :
      ((1/10^24 : ℂ) • Cast.complexMatrix C-
        ((p : ℂ)/(d : ℂ)) • (Cast.complexMatrix A*((1/10^24 : ℂ) • Cast.complexMatrix B))) i j=
        -((p*(A*B) i j-d*C i j : Int) : ℂ)/((d : ℂ)*10^24) := by
    rw [Matrix.mul_smul,smul_smul,← Cast.complexMatrix_mul]
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Cast.complexMatrix,
      Int.cast_sub,Int.cast_mul]
    field_simp
    ring
  apply (matrix_norm_from_entries _ (1/10^24) (by norm_num) ?_).trans (by norm_num)
  intro i j
  rw [entry,neg_div,norm_neg]
  exact integer_ratio_norm _ _ positive (bound i j)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
