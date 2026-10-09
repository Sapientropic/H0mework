import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.TensorReindex

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem energy_tensor_sub_left (O : Matrix (ι × κ) (ι × κ) ℂ) (A C : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    energy O (Matrix.kronecker A B)-energy O (Matrix.kronecker C B)=energy O (Matrix.kronecker (A-C) B) := by
  have delta : Matrix.kronecker A B-Matrix.kronecker C B=Matrix.kronecker (A-C) B := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,sub_mul]
  rw [← delta]
  simp only [energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]

omit [DecidableEq ι] [DecidableEq κ] in
theorem energy_tensor_sub_right (O : Matrix (ι × κ) (ι × κ) ℂ) (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) :
    energy O (Matrix.kronecker A B)-energy O (Matrix.kronecker A C)=energy O (Matrix.kronecker A (B-C)) := by
  have delta : Matrix.kronecker A B-Matrix.kronecker A C=Matrix.kronecker A (B-C) := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,mul_sub]
  rw [← delta]
  simp only [energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]

omit [Fintype κ] [DecidableEq κ] in
theorem energy_dimension_norm (O A : Matrix ι ι ℂ) :
    |energy O A| ≤ (Fintype.card ι : ℝ)*‖O‖*‖A‖ := by
  apply (Complex.abs_re_le_norm (O*A).trace).trans
  exact (Donor.trace_norm_bound (O*A)).trans (by
    have bound := mul_le_mul_of_nonneg_left (norm_mul_le O A) (show (0 : ℝ) ≤ Fintype.card ι by positivity)
    simpa only [mul_assoc] using bound)

theorem tensor_right_operator_error (O : Matrix (ι × κ) (ι × κ) ℂ) (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) :
    |energy O (Matrix.kronecker A B)-energy O (Matrix.kronecker A C)| ≤
      ((Fintype.card ι : ℝ)*Fintype.card κ)*‖O‖*(‖A‖*‖B-C‖) := by
  rw [energy_tensor_sub_right]
  have bound := energy_dimension_norm O (Matrix.kronecker A (B-C))
  rw [Fintype.card_prod,Nat.cast_mul] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left (kronecker_norm_le _ _) (by positivity))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
