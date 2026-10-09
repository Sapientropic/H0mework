import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.States

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface Collision Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def computedPreparation : JointMatrix Basis := Matrix.kronecker computedSystem computedBath
def computedPair : JointMatrix Basis := Input.finiteCollisionMatrix*computedPreparation*star Input.finiteCollisionMatrix

theorem preparation_numeric_error : ‖Diagonal.computedPreparation-computedPreparation‖ ≤ (5/10^16 : ℝ) := by
  have split : Diagonal.computedPreparation-computedPreparation=
      Matrix.kronecker (Diagonal.computedSystem-computedSystem) Diagonal.computedBath+
        Matrix.kronecker computedSystem (Diagonal.computedBath-computedBath) := by
    ext i j
    simp only [Diagonal.computedPreparation,computedPreparation,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,Matrix.add_apply]
    ring
  rw [split]
  have first := (kronecker_norm_le (Diagonal.computedSystem-computedSystem) Diagonal.computedBath).trans
    (mul_le_mul system_numeric_error Diagonal.computed_bath_norm (norm_nonneg _) (by norm_num))
  have second := (kronecker_norm_le computedSystem (Diagonal.computedBath-computedBath)).trans
    (mul_le_mul computed_system_norm bath_numeric_error (norm_nonneg _) (by norm_num))
  exact (norm_add_le _ _).trans ((add_le_add first second).trans (by norm_num))

theorem pair_numeric_error : ‖Diagonal.computedPair-computedPair‖ ≤ (2/10^15 : ℝ) := by
  have paid := Input.raw_input_error Input.finiteCollisionMatrix Diagonal.computedPreparation computedPreparation
  exact paid.trans ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) Diagonal.finite_collision_norm 2)
    preparation_numeric_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

def computedBodyInput : LoadedJoint := Matrix.kronecker (chargedInput computedPair) Prepared.finiteEnvironment
def computedBody : LoadedJoint := Actions.finiteReceivedWord*computedBodyInput*star Actions.finiteReceivedWord

theorem body_input_error : ‖Diagonal.computedBodyInput-computedBodyInput‖ ≤ (4/10^15 : ℝ) := by
  have split : Diagonal.computedBodyInput-computedBodyInput=
      Matrix.kronecker (chargedInput (Diagonal.computedPair-computedPair)) Prepared.finiteEnvironment := by
    ext i j
    simp only [Diagonal.computedBodyInput,computedBodyInput,chargedInput,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [split]
  exact (kronecker_norm_le _ _).trans ((mul_le_mul ((Actions.charged_norm _).trans pair_numeric_error)
    Diagonal.finite_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem body_numeric_error : ‖Diagonal.computedBody-computedBody‖ ≤ (16/10^15 : ℝ) := by
  have wordNorm : ‖Actions.finiteReceivedWord‖ ≤ 2 :=
    (Input.approximated_unitary_norm Actions.calculatedReceivedWord Actions.finiteReceivedWord _ Actions.original_received_word_polynomial_error).trans (by norm_num)
  have paid := Input.raw_input_error Actions.finiteReceivedWord Diagonal.computedBodyInput computedBodyInput
  exact paid.trans ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) wordNorm 2) body_input_error
    (norm_nonneg _) (by norm_num)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
