import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Preparation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
open Collision Propagation.Interface Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem finite_pair_norm : ‖Input.finitePair‖ ≤ 3 := by
  have normV := Input.approximated_unitary_norm Input.mergedUnitary Input.finiteCollisionMatrix _ Input.finite_collision_matrix_error
  have action := Input.raw_conjugation_error Input.mergedUnitary Input.finiteCollisionMatrix Input.finitePreparation
  have first : ‖Quantum.conjugation Input.mergedUnitary Input.finitePreparation‖ ≤ 2 := by
    exact (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (JointMatrix Basis) Input.mergedUnitary) Input.finitePreparation).le.trans Input.finite_preparation_norm
  have paid : ‖Quantum.conjugation Input.mergedUnitary Input.finitePreparation-Input.finitePair‖ ≤
      (1+(1+(3/10^17 : ℝ)))*2*(3/10^17 : ℝ) := by
    apply action.trans
    exact mul_le_mul
      (mul_le_mul (add_le_add le_rfl normV) Input.finite_preparation_norm (norm_nonneg _) (by norm_num))
      Input.finite_collision_matrix_error (norm_nonneg _) (by norm_num)
  have triangle := norm_sub_le_norm_sub_add_norm_sub Input.finitePair
    (Quantum.conjugation Input.mergedUnitary Input.finitePreparation) 0
  simp only [sub_zero] at triangle
  rw [norm_sub_rev] at paid
  linarith

theorem charged_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (rho : Matrix ι ι ℂ) :
    ‖chargedInput rho‖ ≤ ‖rho‖ := by
  exact (kronecker_norm_le rho excitedController).trans (by
    have bound := mul_le_mul_of_nonneg_left
      (Input.state_norm_le_one excitedController excitedController_positive excitedController_trace) (norm_nonneg rho)
    simpa only [mul_one] using bound)

theorem prepared_input_norm : ‖preparedInput‖ ≤ 3 := by
  apply (kronecker_norm_le (chargedInput Input.finitePair) environmentState).trans
  have p := mul_le_mul (charged_norm Input.finitePair |>.trans finite_pair_norm)
    (Input.state_norm_le_one environmentState environmentState_positive environmentState_trace) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  simpa only [mul_one] using p

def finitePreparedInput : LoadedJoint := Matrix.kronecker (chargedInput Input.finitePair) Prepared.finiteEnvironment
def finiteReceivedBody : LoadedJoint := finiteReceivedWord*finitePreparedInput*star finiteReceivedWord

theorem prepared_environment_error : ‖preparedInput-finitePreparedInput‖ ≤ (21/10^18 : ℝ) := by
  have split : preparedInput-finitePreparedInput=
      Matrix.kronecker (chargedInput Input.finitePair) (environmentState-Prepared.finiteEnvironment) := by
    ext i j
    simp only [preparedInput,finitePreparedInput,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [split]
  apply (kronecker_norm_le _ _).trans
  exact (mul_le_mul (charged_norm Input.finitePair |>.trans finite_pair_norm)
    Prepared.original_finite_environment_error (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)).trans (by norm_num)

theorem finite_received_body_error :
    ‖Quantum.conjugation calculatedReceivedWord preparedInput-finiteReceivedBody‖ ≤ (3/10^12 : ℝ) := by
  have normV := Input.approximated_unitary_norm calculatedReceivedWord finiteReceivedWord _ original_received_word_polynomial_error
  have action := Input.raw_conjugation_error calculatedReceivedWord finiteReceivedWord preparedInput
  have input := Input.raw_input_error finiteReceivedWord preparedInput finitePreparedInput
  have actionBound : ‖Quantum.conjugation calculatedReceivedWord preparedInput-finiteReceivedWord*preparedInput*star finiteReceivedWord‖ ≤
      (1+(1+(4/10^13 : ℝ)))*3*(4/10^13 : ℝ) := by
    apply action.trans
    exact mul_le_mul (mul_le_mul (add_le_add le_rfl normV) prepared_input_norm (norm_nonneg _) (by norm_num))
      original_received_word_polynomial_error (norm_nonneg _) (by norm_num)
  have inputBound : ‖finiteReceivedWord*preparedInput*star finiteReceivedWord-finiteReceivedBody‖ ≤
      (1+(4/10^13 : ℝ))^2*(21/10^18 : ℝ) := by
    apply input.trans
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) normV 2) prepared_environment_error (norm_nonneg _) (by positivity)
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Quantum.conjugation calculatedReceivedWord preparedInput)
    (finiteReceivedWord*preparedInput*star finiteReceivedWord) finiteReceivedBody
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
