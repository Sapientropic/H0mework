import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Hybrid
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.TensorBudget

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem big_bath_energy_error (O : JointMatrix Basis) :
    |energy O (Matrix.kronecker calculatedSystem calculatedBath)-energy O (Matrix.kronecker calculatedSystem hybridBath)| ≤
      (392/10^8 : ℝ)*‖O‖ := by
  rw [energy_tensor_sub_right]
  have paid := tensor_energy_norm_right O (calculatedBath-hybridBath) calculatedSystem
    (calculated_bath_lawful.1.isHermitian.sub hybrid_bath_lawful.1.isHermitian) calculated_system_lawful.1
  rw [calculated_system_lawful.2,Complex.one_re,mul_one] at paid
  apply paid.trans
  have cost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hybrid_bath_error (show (0 : ℝ) ≤ Fintype.card Basis by positivity)) (norm_nonneg O)
  norm_num [Basis] at cost ⊢
  exact cost

theorem system_energy_error (O : JointMatrix Basis) :
    |energy O (Matrix.kronecker calculatedSystem hybridBath)-energy O (Matrix.kronecker finiteSystem hybridBath)| ≤
      (1274/10^11 : ℝ)*‖O‖ := by
  rw [energy_tensor_sub_left]
  have paid := tensor_energy_norm O (calculatedSystem-finiteSystem) hybridBath
    (calculated_system_lawful.1.isHermitian.sub finite_system_positive.isHermitian) hybrid_bath_lawful.1
  rw [hybrid_bath_lawful.2,Complex.one_re,mul_one] at paid
  apply paid.trans
  have cost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left finite_system_error (show (0 : ℝ) ≤ Fintype.card Basis by positivity)) (norm_nonneg O)
  norm_num [Basis] at cost ⊢
  exact cost

theorem finite_system_norm : ‖finiteSystem‖ ≤ 1+(13/10^11 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub finiteSystem calculatedSystem 0
  simp only [sub_zero] at triangle
  have distance := finite_system_error
  rw [norm_sub_rev] at distance
  linarith [state_norm_le_one calculatedSystem calculated_system_lawful.1 calculated_system_lawful.2]

theorem small_bath_energy_error (O : JointMatrix Basis) :
    |energy O (Matrix.kronecker finiteSystem hybridBath)-energy O (Matrix.kronecker finiteSystem finiteBath)| ≤
      (5/10^8 : ℝ)*‖O‖ := by
  have paid := tensor_right_operator_error O finiteSystem hybridBath finiteBath
  norm_num [Basis] at paid
  apply paid.trans
  calc
    _ ≤ 9604*‖O‖*((1+(13/10^11 : ℝ))*(5/10^12 : ℝ)) := by
      gcongr
      · exact finite_system_norm
      · exact hybrid_finite_bath_error
    _ ≤ _ := by nlinarith [norm_nonneg O]

theorem source_preparation_energy_error (O : JointMatrix Basis) :
    |energy O (Matrix.kronecker calculatedSystem calculatedBath)-energy O (Matrix.kronecker finiteSystem finiteBath)| ≤
      (5/10^6 : ℝ)*‖O‖ := by
  have first := abs_sub_le (energy O (Matrix.kronecker calculatedSystem calculatedBath))
    (energy O (Matrix.kronecker calculatedSystem hybridBath)) (energy O (Matrix.kronecker finiteSystem finiteBath))
  have second := abs_sub_le (energy O (Matrix.kronecker calculatedSystem hybridBath))
    (energy O (Matrix.kronecker finiteSystem hybridBath)) (energy O (Matrix.kronecker finiteSystem finiteBath))
  nlinarith [big_bath_energy_error O,system_energy_error O,small_bath_energy_error O,norm_nonneg O]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
