import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.OriginalNorms
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.Tensor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem computed_pc_norm : ‖Primitive.computedPC‖ ≤ 3 :=
  (close_norm _ _ _ _ original_pc_norm Primitive.original_computed_PC).trans (by norm_num)

theorem free_error : ‖Phase.freePolynomial-free‖ ≤ (8/10^24 : ℝ) :=
  (tensor_left_change Phase.pcPolynomial Primitive.computedPC Phase.environmentPolynomial).trans
    ((mul_le_mul Primitive.original_computed_PC original_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem parent_error : ‖Actions.parentPolynomial-parent‖ ≤ (4/10^24 : ℝ) := by
  have bound := tensor_left_change Actions.parentPCPolynomial Primitive.computedParentPC (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [norm_one,mul_one] at bound
  exact bound.trans Primitive.original_computed_parent_PC

theorem recovery_error : ‖Actions.recoveryPolynomial-recovery‖ ≤ (8/10^24 : ℝ) :=
  (tensor_left_change Actions.recoveryPCPolynomial Primitive.computedRecoveryPC Actions.recoveryEnvironmentPolynomial).trans
    ((mul_le_mul Primitive.original_computed_recovery_PC original_recovery_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem free_norm : ‖free‖ ≤ 3 := (close_norm _ _ _ _ original_free_norm free_error).trans (by norm_num)
theorem parent_norm : ‖parent‖ ≤ 3 := (close_norm _ _ _ _ original_parent_norm parent_error).trans (by norm_num)
theorem recovery_norm : ‖recovery‖ ≤ 3 := (close_norm _ _ _ _ original_recovery_norm recovery_error).trans (by norm_num)

attribute [local irreducible] Actions.recoveryPolynomial Actions.loadPolynomial Actions.parentPolynomial recovery parent

theorem received_word_error : ‖Actions.finiteReceivedWord-receivedWord‖ ≤ (1/10^22 : ℝ) := by
  have first : ‖Actions.recoveryPolynomial*Actions.loadPolynomial-recovery*Actions.loadPolynomial‖ ≤ (16/10^24 : ℝ) := by
    rw [← Matrix.sub_mul]
    exact (norm_mul_le (Actions.recoveryPolynomial-recovery) Actions.loadPolynomial).trans ((mul_le_mul recovery_error original_load_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have middle : ‖recovery*Actions.loadPolynomial‖ ≤ 6 :=
    (norm_mul_le recovery Actions.loadPolynomial).trans ((mul_le_mul recovery_norm original_load_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have bound := product_change (Actions.recoveryPolynomial*Actions.loadPolynomial) Actions.parentPolynomial
    (recovery*Actions.loadPolynomial) parent
  exact bound.trans ((add_le_add
    (mul_le_mul first original_parent_norm (norm_nonneg _) (by norm_num))
    (mul_le_mul middle parent_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem received_word_norm : ‖receivedWord‖ ≤ 3 :=
  (close_norm _ _ _ _ original_received_norm received_word_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
