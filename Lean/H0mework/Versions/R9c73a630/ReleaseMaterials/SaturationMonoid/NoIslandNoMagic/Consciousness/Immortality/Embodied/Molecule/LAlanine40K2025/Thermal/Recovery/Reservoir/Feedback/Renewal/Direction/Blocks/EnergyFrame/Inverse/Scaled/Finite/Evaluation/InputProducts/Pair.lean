import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.States

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface Collision Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def preparation : JointMatrix Basis := Matrix.kronecker system bath
def pair : JointMatrix Basis := Input.finiteCollisionMatrix*preparation*star Input.finiteCollisionMatrix
def bodyInput : LoadedJoint := Matrix.kronecker (chargedInput pair) Prepared.finiteEnvironment
def body : LoadedJoint := LoadExecution.receivedWord*bodyInput*star LoadExecution.receivedWord

theorem preparation_error : ‖Field.computedPreparation-preparation‖ ≤ (4/10^21 : ℝ) :=
  (PCExecution.tensor_change Field.computedSystem system Field.computedBath bath).trans
    ((add_le_add (mul_le_mul system_error old_bath_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul system_norm bath_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem pair_error : ‖Field.computedPair-pair‖ ≤ (2/10^20 : ℝ) :=
  (Input.raw_input_error Input.finiteCollisionMatrix Field.computedPreparation preparation).trans
    ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) Diagonal.finite_collision_norm 2) preparation_error
      (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem body_input_error : ‖Field.computedBodyInput-bodyInput‖ ≤ (4/10^20 : ℝ) := by
  have same : Field.computedBodyInput-bodyInput=
      Matrix.kronecker (chargedInput (Field.computedPair-pair)) Prepared.finiteEnvironment := by
    ext i j
    simp only [Field.computedBodyInput,bodyInput,chargedInput,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [same]
  exact (kronecker_norm_le _ _).trans ((mul_le_mul ((Actions.charged_norm _).trans pair_error)
    Diagonal.finite_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem body_error : ‖LoadExecution.receivedBody-body‖ ≤ (7/10^19 : ℝ) :=
  (Input.raw_input_error LoadExecution.receivedWord Field.computedBodyInput bodyInput).trans
    ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) LoadExecution.received_word_norm 2) body_input_error
      (norm_nonneg _) (by norm_num)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
