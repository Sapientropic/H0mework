import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Normalization

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Collision Propagation.Interface Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def computedSystemWord : Matrix Basis Basis ℂ := Input.fieldPolynomial*activeMatrix
def computedSystem : Matrix Basis Basis ℂ := computedSystemWord*Input.rawBaseSystem*star computedSystemWord
def computedBath : Matrix Basis Basis ℂ := Input.fieldPolynomial*computedGibbs*star Input.fieldPolynomial

theorem field_polynomial_norm : ‖Input.fieldPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm
    (Input.singleUnitary Input.calculatedFieldHamiltonian Input.calculated_field_hermitian (nativeClockStep : ℝ))
    Input.fieldPolynomial _ Input.field_polynomial_error).trans (by norm_num)

theorem system_word_numeric_error : ‖Input.finiteSystemWord-computedSystemWord‖ ≤ (4/10^18 : ℝ) := by
  change ‖Input.fieldPolynomial*Input.activePolynomial-Input.fieldPolynomial*activeMatrix‖ ≤ _
  rw [← Matrix.mul_sub]
  exact (norm_mul_le _ _).trans ((mul_le_mul field_polynomial_norm actual_active_matrix_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem exact_system_word_norm : ‖Input.finiteSystemWord‖ ≤ 2 :=
  (Input.approximated_unitary_norm Input.calculatedSystemWord Input.finiteSystemWord _ Input.finite_system_word_error).trans (by norm_num)

theorem computed_system_word_norm : ‖computedSystemWord‖ ≤ 3 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub computedSystemWord Input.finiteSystemWord 0
  simp only [sub_zero] at triangle
  have difference := system_word_numeric_error
  rw [norm_sub_rev] at difference
  linarith [exact_system_word_norm]

theorem raw_base_norm : ‖Input.rawBaseSystem‖ ≤ 2 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub Input.rawBaseSystem Input.calculatedBaseSystem 0
  simp only [sub_zero] at triangle
  have difference := Input.raw_base_system_error
  rw [norm_sub_rev] at difference
  linarith [Input.calculated_base_norm]

theorem exact_computed_system_error : ‖Input.finiteSystem-computedSystem‖ ≤ (4/10^17 : ℝ) := by
  have paid := Post.raw_sandwich_change (star Input.finiteSystemWord) (star computedSystemWord) Input.rawBaseSystem
  simp only [star_star,norm_star,← star_sub] at paid
  apply paid.trans
  exact (mul_le_mul (mul_le_mul (add_le_add exact_system_word_norm computed_system_word_norm) raw_base_norm (norm_nonneg _) (by norm_num))
    system_word_numeric_error (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem exact_computed_bath_error : ‖Input.finiteBath-computedBath‖ ≤ (2/10^17 : ℝ) := by
  have paid := Input.raw_input_error Input.fieldPolynomial Input.finiteGibbs computedGibbs
  apply paid.trans
  exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) field_polynomial_norm 2) original_computed_gibbs_error (norm_nonneg _) (by norm_num)).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
