import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.BaseErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision Load.Producer.StrictThermal
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem field_pair_norm : ‖Field.computedPair‖ ≤ 4 := by
  have earlier := close_norm Input.finitePair Diagonal.computedPair 3 (5/10^16) Actions.finite_pair_norm Diagonal.pair_numeric_error
  have next := close_norm Diagonal.computedPair Field.computedPair (3+5/10^16) (2/10^15) earlier Field.pair_numeric_error
  exact next.trans (by norm_num)

theorem body_input_norm : ‖Field.computedBodyInput‖ ≤ 8 :=
  (kronecker_norm_le _ _).trans ((mul_le_mul ((Actions.charged_norm _).trans field_pair_norm)
    Diagonal.finite_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

private theorem forward_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    ‖A*B*star A‖ ≤ ‖A‖^2*‖B‖ := by
  have bound := Prepared.sandwich_norm (star A) B
  simpa only [star_star,norm_star] using bound

theorem field_body_norm : ‖Field.computedBody‖ ≤ 32 :=
  (forward_norm Actions.finiteReceivedWord Field.computedBodyInput).trans
    ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) original_received_norm 2)
      body_input_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem body_error : ‖Field.computedBody-receivedBody‖ ≤ (4/10^21 : ℝ) := by
  have bound := Post.raw_sandwich_change (star Actions.finiteReceivedWord) (star receivedWord) Field.computedBodyInput
  simp only [star_star,norm_star,← star_sub] at bound
  exact bound.trans ((mul_le_mul (mul_le_mul (add_le_add original_received_norm received_word_norm)
    body_input_norm (norm_nonneg _) (by norm_num)) received_word_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
