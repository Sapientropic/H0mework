import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision Propagation.Producer
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem original_pc_norm : ‖Phase.pcPolynomial‖ ≤ 2 := Phase.pc_polynomial_norm.trans (by norm_num)

theorem original_environment_norm : ‖Phase.environmentPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))
    Phase.environmentPolynomial _ Phase.environment_polynomial_error).trans (by norm_num)

theorem original_free_norm : ‖Phase.freePolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm numericFree Phase.freePolynomial _ Phase.numeric_free_polynomial_error).trans (by norm_num)

theorem original_parent_norm : ‖Actions.parentPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm (Actions.reframeUnitary installedLoadFrame Actions.parentWord)
    Actions.parentPolynomial _ Actions.original_parent_polynomial_error).trans (by norm_num)

theorem original_recovery_norm : ‖Actions.recoveryPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm (Actions.reframeUnitary installedLoadFrame Actions.recoveryWord)
    Actions.recoveryPolynomial _ Actions.original_recovery_polynomial_error).trans (by norm_num)

theorem original_recovery_environment_norm : ‖Actions.recoveryEnvironmentPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm (Load.Recovery.Control.environmentUnitary (3*(nativeClockStep : ℝ)))
    Actions.recoveryEnvironmentPolynomial _ Actions.original_recovery_environment_polynomial_error).trans (by norm_num)

theorem original_load_norm : ‖Actions.loadPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm (Actions.reframeUnitary installedLoadFrame (loadUnitary (nativeClockStep : ℝ)))
    Actions.loadPolynomial _ Actions.original_load_polynomial_error).trans (by norm_num)

theorem original_received_norm : ‖Actions.finiteReceivedWord‖ ≤ 2 :=
  (Input.approximated_unitary_norm Actions.calculatedReceivedWord Actions.finiteReceivedWord _ Actions.original_received_word_polynomial_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
