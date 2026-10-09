import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.RawCoordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem approximated_unitary_norm (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (d : ℝ)
    (paid : ‖(U : Matrix ι ι ℂ)-A‖ ≤ d) : ‖A‖ ≤ 1+d := by
  have t := norm_sub_le_norm_sub_add_norm_sub A (U : Matrix ι ι ℂ) 0
  simp only [sub_zero,CStarRing.norm_coe_unitary] at t
  rw [norm_sub_rev] at paid
  linarith

theorem approximated_product_error (U V : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) (d e : ℝ)
    (left : ‖(U : Matrix ι ι ℂ)-A‖ ≤ d) (right : ‖(V : Matrix ι ι ℂ)-B‖ ≤ e) :
    ‖((U*V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)-A*B‖ ≤ d+(1+d)*e := by
  have split : ((U*V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)-A*B=
      ((U : Matrix ι ι ℂ)-A)*(V : Matrix ι ι ℂ)+A*((V : Matrix ι ι ℂ)-B) := by
    change (U : Matrix ι ι ℂ)*(V : Matrix ι ι ℂ)-A*B=_
    noncomm_ring
  rw [split]
  apply (norm_add_le _ _).trans
  rw [CStarRing.norm_mul_coe_unitary]
  apply add_le_add left
  exact (norm_mul_le _ _).trans (mul_le_mul (approximated_unitary_norm U A d left) right (norm_nonneg _) (by linarith [norm_nonneg A,approximated_unitary_norm U A d left]))

omit [Nonempty ι] in
theorem raw_input_error (V A B : Matrix ι ι ℂ) :
    ‖V*A*star V-V*B*star V‖ ≤ ‖V‖^2*‖A-B‖ := by
  have split : V*A*star V-V*B*star V=V*(A-B)*star V := by noncomm_ring
  rw [split]
  calc
    _ ≤ (‖V‖*‖A-B‖)*‖star V‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ = _ := by rw [norm_star]; ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
