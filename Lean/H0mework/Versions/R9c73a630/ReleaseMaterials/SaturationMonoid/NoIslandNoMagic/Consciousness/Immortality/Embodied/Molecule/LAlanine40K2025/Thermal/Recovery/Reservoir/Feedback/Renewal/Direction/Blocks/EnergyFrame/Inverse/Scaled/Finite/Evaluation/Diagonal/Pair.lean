import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Collision Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def computedPreparation : JointMatrix Basis := Matrix.kronecker computedSystem computedBath
def computedPair : JointMatrix Basis := Input.finiteCollisionMatrix*computedPreparation*star Input.finiteCollisionMatrix

theorem original_finite_system_norm : ‖Input.finiteSystem‖ ≤ 2 := Input.finite_system_norm.trans (by norm_num)
theorem original_finite_bath_norm : ‖Input.finiteBath‖ ≤ 2 := Input.finite_bath_norm.trans (by norm_num)

theorem computed_system_norm : ‖computedSystem‖ ≤ 2 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub computedSystem Input.finiteSystem 0
  simp only [sub_zero] at triangle
  have paid := exact_computed_system_error
  rw [norm_sub_rev] at paid
  linarith [Input.finite_system_norm]

theorem computed_bath_norm : ‖computedBath‖ ≤ 2 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub computedBath Input.finiteBath 0
  simp only [sub_zero] at triangle
  have paid := exact_computed_bath_error
  rw [norm_sub_rev] at paid
  linarith [Input.finite_bath_norm]

theorem preparation_numeric_error : ‖Input.finitePreparation-computedPreparation‖ ≤ (12/10^17 : ℝ) := by
  have split : Input.finitePreparation-computedPreparation=
      Matrix.kronecker (Input.finiteSystem-computedSystem) Input.finiteBath+
        Matrix.kronecker computedSystem (Input.finiteBath-computedBath) := by
    ext i j
    simp only [Input.finitePreparation,computedPreparation,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,Matrix.add_apply]
    ring
  rw [split]
  have first := (Load.Producer.StrictThermal.kronecker_norm_le (Input.finiteSystem-computedSystem) Input.finiteBath).trans
    (mul_le_mul exact_computed_system_error original_finite_bath_norm (norm_nonneg _) (by norm_num))
  have second := (Load.Producer.StrictThermal.kronecker_norm_le computedSystem (Input.finiteBath-computedBath)).trans
    (mul_le_mul computed_system_norm exact_computed_bath_error (norm_nonneg _) (by norm_num))
  exact (norm_add_le _ _).trans ((add_le_add first second).trans (by norm_num))

theorem finite_collision_norm : ‖Input.finiteCollisionMatrix‖ ≤ 2 :=
  (Input.approximated_unitary_norm Input.mergedUnitary Input.finiteCollisionMatrix _ Input.finite_collision_matrix_error).trans (by norm_num)

theorem pair_numeric_error : ‖Input.finitePair-computedPair‖ ≤ (5/10^16 : ℝ) := by
  have paid := Input.raw_input_error Input.finiteCollisionMatrix Input.finitePreparation computedPreparation
  exact paid.trans ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) finite_collision_norm 2) preparation_numeric_error
    (norm_nonneg _) (by norm_num)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
