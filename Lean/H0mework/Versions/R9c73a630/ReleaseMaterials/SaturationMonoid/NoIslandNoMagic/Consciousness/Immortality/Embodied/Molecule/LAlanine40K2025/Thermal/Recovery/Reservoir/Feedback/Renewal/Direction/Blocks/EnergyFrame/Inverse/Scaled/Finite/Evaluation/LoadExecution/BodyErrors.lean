import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.ActionErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem body_error : ‖PCExecution.receivedBody-receivedBody‖ ≤ (2/10^21 : ℝ) := by
  have h := Post.raw_sandwich_change (star PCExecution.receivedWord) (star receivedWord) Field.computedBodyInput
  simp only [star_star,norm_star,← star_sub] at h
  exact h.trans ((mul_le_mul (mul_le_mul (add_le_add PCExecution.received_word_norm received_word_norm)
    PCExecution.body_input_norm (norm_nonneg _) (by norm_num)) received_word_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem old_body_norm : ‖PCExecution.receivedBody‖ ≤ 33 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.field_body_norm PCExecution.body_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
