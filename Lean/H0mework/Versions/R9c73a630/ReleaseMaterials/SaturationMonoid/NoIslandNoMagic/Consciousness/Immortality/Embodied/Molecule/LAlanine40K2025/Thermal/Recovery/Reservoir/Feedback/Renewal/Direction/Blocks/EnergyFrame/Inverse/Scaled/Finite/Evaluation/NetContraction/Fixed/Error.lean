import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Norm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

private theorem pair_error (x y : Int) :
    ‖(((scale*round x-x : Int) : ℂ)+Complex.I*((scale*round y-y : Int) : ℂ))/(scale : ℂ)^2‖ ≤ (1/10^30 : ℝ) := by
  have xi := round_residual x
  have yi := round_residual y
  have bound : |scale*round x-x|+|scale*round y-y| ≤ scale := by
    rw [abs_sub_comm (scale*round x),abs_sub_comm (scale*round y)]
    omega
  have size := (InputProducts.integer_pair_norm (scale*round x-x) (scale*round y-y)).trans
    (show ((|scale*round x-x|+|scale*round y-y| : Int) : ℝ) ≤ (scale : ℝ) by exact_mod_cast bound)
  rw [norm_div,norm_pow,Complex.norm_intCast]
  norm_num [scale] at size ⊢
  linarith

variable {α β γ : Type*} [Fintype β]

theorem multiply_entry_error (A : MatrixInt α β) (B : MatrixInt β γ) (i : α) (j : γ) :
    ‖(value (multiply A B)-value A*value B) i j‖ ≤ (1/10^30 : ℝ) := by
  have same : (value (multiply A B)-value A*value B) i j=
      (((scale*round ((A.re*B.re-A.im*B.im) i j)-(A.re*B.re-A.im*B.im) i j : Int) : ℂ)+
        Complex.I*((scale*round ((A.re*B.im+A.im*B.re) i j)-(A.re*B.im+A.im*B.re) i j : Int) : ℂ))/(scale : ℂ)^2 := by
    unfold value
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,raw_mul]
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,raw,multiply,Int.cast_sub,Int.cast_mul]
    field_simp
    ring
  rw [same]
  exact pair_error _ _

theorem multiply_error [Fintype α] [Fintype γ] [DecidableEq γ]
    (A : MatrixInt α β) (B : MatrixInt β γ) (rows : Fintype.card α ≤ 64) (cols : Fintype.card γ ≤ 64) :
    ‖value (multiply A B)-value A*value B‖ ≤ (64/10^30 : ℝ) := by
  simpa only [mul_one_div] using norm_from_entries _ (1/10^30) (by norm_num) rows cols (multiply_entry_error A B)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
