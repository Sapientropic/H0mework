import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Net

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem product_change (A B C D : Matrix ι ι ℂ) :
    ‖A*B-C*D‖ ≤ ‖A-C‖*‖B‖+‖C‖*‖B-D‖ := by
  have split : A*B-C*D=(A-C)*B+C*(B-D) := by noncomm_ring
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

theorem close_norm (A B : Matrix ι ι ℂ) (a d : ℝ) (bounded : ‖A‖ ≤ a) (near : ‖A-B‖ ≤ d) : ‖B‖ ≤ a+d := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub B A 0
  simp only [sub_zero] at triangle
  rw [norm_sub_rev B A] at triangle
  linarith

theorem raw_pair_pullback (A B O P : Matrix ι ι ℂ) :
    ‖star A*O*A-star B*P*B‖ ≤ (‖A‖+‖B‖)*‖O‖*‖A-B‖+‖B‖^2*‖O-P‖ := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub (star A*O*A) (star B*O*B) (star B*P*B)
  have first := Post.raw_sandwich_change A B O
  have second := Input.raw_input_error (star B) O P
  simp only [star_star,norm_star] at second
  exact triangle.trans (add_le_add first second)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
