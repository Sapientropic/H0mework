import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.SupplyErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision Propagation.Producer
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem load_error : ‖Post.fullLoadPolynomial-load‖ ≤ (8/10^24 : ℝ) := by
  rw [Post.fullLoadPolynomial,load,Post.local_matrix_sub,Finite.reindex_norm]
  have bound := tensor_change Actions.loadPolynomial Actions.loadPolynomial Phase.pcPolynomial Primitive.computedPC
  simp only [sub_self,norm_zero,zero_mul,zero_add] at bound
  exact bound.trans ((mul_le_mul original_load_norm Primitive.original_computed_PC (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem pointer_phase_norm : ‖Phase.pointerPhase‖ ≤ 2 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub Phase.pointerPhase (freePhase (nativeClockStep : ℝ) : ℂ) 0
  simp only [sub_zero,CStarRing.norm_coe_unitary] at triangle
  have bound := Phase.original_phase_error
  rw [norm_sub_rev] at bound
  linarith

private theorem controlled_change (A B C D : Current.FullJoint) :
    ‖Matrix.fromBlocks A 0 0 (Phase.pointerPhase • B)-Matrix.fromBlocks C 0 0 (Phase.pointerPhase • D)‖ ≤
      max ‖A-C‖ (2*‖B-D‖) := by
  have bound := Post.blocks_error A (Phase.pointerPhase • B) C (Phase.pointerPhase • D)
  rw [← smul_sub,norm_smul] at bound
  exact bound.trans (max_le_max le_rfl (mul_le_mul_of_nonneg_right pointer_phase_norm (norm_nonneg _)))

theorem pointer_load_error : ‖Post.pointerLoadPolynomial-pointerLoad‖ ≤ (2/10^22 : ℝ) :=
  (controlled_change Post.fullLoadPolynomial Post.fullLoadPolynomial load load).trans
    ((max_le_max load_error (mul_le_mul_of_nonneg_left load_error (by norm_num))).trans (by norm_num))

theorem pointer_supply_error : ‖Post.pointerFeedbackPolynomial-pointerSupply‖ ≤ (2/10^22 : ℝ) :=
  (controlled_change Post.fullLoadPolynomial Supply.fullSupplyPolynomial load supply).trans
    ((max_le_max load_error (mul_le_mul_of_nonneg_left supply_error (by norm_num))).trans (by norm_num))

theorem pointer_weak_error : ‖Post.pointerWeakPolynomial-pointerWeak‖ ≤ (2/10^22 : ℝ) :=
  (controlled_change Post.fullLoadPolynomial Post.fullWeakPolynomial load weak).trans
    ((max_le_max load_error (mul_le_mul_of_nonneg_left weak_error (by norm_num))).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
