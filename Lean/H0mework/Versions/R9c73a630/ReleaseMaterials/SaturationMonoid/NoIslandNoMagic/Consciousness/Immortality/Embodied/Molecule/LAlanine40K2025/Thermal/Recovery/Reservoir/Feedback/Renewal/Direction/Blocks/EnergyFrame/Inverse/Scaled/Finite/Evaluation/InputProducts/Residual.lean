import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Complex

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem integer_pair_norm (a b : Int) : ‖(a : ℂ)+Complex.I*(b : ℂ)‖ ≤ (|a|+|b| : Int) := by
  have h := norm_add_le (a : ℂ) (Complex.I*(b : ℂ))
  simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_intCast,Int.cast_add,Int.cast_abs] using h

theorem integer_pair_ratio_norm (a b d : Int) (positive : 0 < d) (bound : |a|+|b| ≤ d) :
    ‖((a : ℂ)+Complex.I*(b : ℂ))/((d : ℂ)*10^24)‖ ≤ (1/10^24 : ℝ) := by
  have dp : (0 : ℝ) < d := by exact_mod_cast positive
  have h := (integer_pair_norm a b).trans (show ((|a|+|b| : Int) : ℝ) ≤ (d : ℝ) by exact_mod_cast bound)
  rw [norm_div,norm_mul,Complex.norm_intCast]
  norm_num
  rw [abs_of_pos dp,div_le_iff₀ (by positivity)]
  nlinarith

theorem complex_product_residual (R I A B C D : Matrix Basis Basis Int) (p d : Int)
    (positive : 0 < d)
    (bound : ∀ i j, |p*(R*A-I*B) i j-d*C i j|+|p*(R*B+I*A) i j-d*D i j| ≤ d) :
    ‖scaledMatrix C D (10^24)-((p : ℂ)/((d : ℂ)*10^24)) • (complexMatrix R I*complexMatrix A B)‖ ≤ (1/10^22 : ℝ) := by
  have dn : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
  have entry (i j : Basis) :
      (scaledMatrix C D (10^24)-((p : ℂ)/((d : ℂ)*10^24)) • (complexMatrix R I*complexMatrix A B)) i j=
        -(((p*(R*A-I*B) i j-d*C i j : Int) : ℂ)+Complex.I*((p*(R*B+I*A) i j-d*D i j : Int) : ℂ))/((d : ℂ)*10^24) := by
    rw [complexMatrix_mul]
    simp only [scaledMatrix,complexMatrix,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    field_simp
    ring
  apply (matrix_norm_from_entries _ (1/10^24) (by norm_num) ?_).trans (by norm_num)
  intro i j
  rw [entry,neg_div,norm_neg]
  exact integer_pair_ratio_norm _ _ _ positive (bound i j)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
