import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem sandwich_difference {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C D : Matrix ι ι ℂ) :
    ‖A*B*D-A*C*D‖ ≤ ‖A‖*‖B-C‖*‖D‖ := by
  rw [← Matrix.sub_mul,← Matrix.mul_sub]
  exact (norm_mul_le (A*(B-C)) D).trans (mul_le_mul_of_nonneg_right (norm_mul_le A (B-C)) (norm_nonneg D))

theorem received_word_error : ‖PCExecution.receivedWord-receivedWord‖ ≤ (2/10^23 : ℝ) :=
  (sandwich_difference PCExecution.recovery Actions.loadPolynomial LoadPrimitive.computedLoad PCExecution.parent).trans
    ((mul_le_mul (mul_le_mul PCExecution.recovery_norm LoadPrimitive.original_computed_load_error
      (norm_nonneg _) (by norm_num)) PCExecution.parent_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem received_word_norm : ‖receivedWord‖ ≤ 4 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.received_word_norm received_word_error).trans (by norm_num)

theorem load_error : ‖PCExecution.load-load‖ ≤ (6/10^24 : ℝ) := by
  rw [PCExecution.load,load,Post.local_matrix_sub,Finite.reindex_norm]
  exact (PCExecution.tensor_left_change Actions.loadPolynomial LoadPrimitive.computedLoad Primitive.computedPC).trans
    ((mul_le_mul LoadPrimitive.original_computed_load_error PCExecution.computed_pc_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem pointer_load_error : ‖PCExecution.pointerLoad-pointerLoad‖ ≤ (12/10^24 : ℝ) := by
  have h := Post.blocks_error PCExecution.load (Phase.pointerPhase • PCExecution.load) load (Phase.pointerPhase • load)
  rw [← smul_sub,norm_smul] at h
  exact h.trans ((max_le_max load_error
    (mul_le_mul PCExecution.pointer_phase_norm load_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem pointer_supply_error : ‖PCExecution.pointerSupply-pointerSupply‖ ≤ (12/10^24 : ℝ) := by
  have h := Post.blocks_error PCExecution.load (Phase.pointerPhase • PCExecution.supply) load (Phase.pointerPhase • PCExecution.supply)
  simp only [sub_self,norm_zero,max_eq_left (norm_nonneg _)] at h
  exact h.trans (load_error.trans (by norm_num))

theorem pointer_weak_error : ‖PCExecution.pointerWeak-pointerWeak‖ ≤ (12/10^24 : ℝ) := by
  have h := Post.blocks_error PCExecution.load (Phase.pointerPhase • PCExecution.weak) load (Phase.pointerPhase • PCExecution.weak)
  simp only [sub_self,norm_zero,max_eq_left (norm_nonneg _)] at h
  exact h.trans (load_error.trans (by norm_num))

theorem pointer_load_norm : ‖pointerLoad‖ ≤ 4 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.pointer_load_norm pointer_load_error).trans (by norm_num)
theorem pointer_supply_norm : ‖pointerSupply‖ ≤ 4 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.pointer_supply_norm pointer_supply_error).trans (by norm_num)
theorem pointer_weak_norm : ‖pointerWeak‖ ≤ 4 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.pointer_weak_norm pointer_weak_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
