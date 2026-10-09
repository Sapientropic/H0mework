import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Coupling

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def finitePreparation : JointMatrix Basis := Matrix.kronecker finiteSystem finiteBath
def finitePair : JointMatrix Basis := finiteCollisionMatrix*finitePreparation*star finiteCollisionMatrix

theorem finite_bath_norm : ‖finiteBath‖ ≤ 1+(41/10^9 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub finiteBath calculatedBath 0
  simp only [sub_zero] at triangle
  have distance := finite_bath_error
  rw [norm_sub_rev] at distance
  linarith [state_norm_le_one calculatedBath calculated_bath_lawful.1 calculated_bath_lawful.2]

theorem finite_preparation_norm : ‖finitePreparation‖ ≤ 2 := by
  have paid := kronecker_norm_le finiteSystem finiteBath
  exact paid.trans (by
    have bound := mul_le_mul finite_system_norm finite_bath_norm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1+13/10^11)
    nlinarith)

set_option maxRecDepth 4096 in
theorem finite_coupling_energy_error (O : JointMatrix Basis) :
    |energy O finiteCollisionPair-energy O finitePair| ≤ (2/10^12 : ℝ)*‖O‖ := by
  have normV := approximated_unitary_norm mergedUnitary finiteCollisionMatrix _ finite_collision_matrix_error
  have action := raw_conjugation_error mergedUnitary finiteCollisionMatrix finitePreparation
  have read : energy O finiteCollisionPair-energy O finitePair=
      energy O (Quantum.conjugation mergedUnitary finitePreparation-finitePair) := by
    simp only [finiteCollisionPair,finitePreparation,energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
  rw [read]
  apply (energy_dimension_norm O _).trans
  have bound : ‖Quantum.conjugation mergedUnitary finitePreparation-finitePair‖ ≤
      (1+(1+(3/10^17 : ℝ)))*2*(3/10^17 : ℝ) := by
    apply action.trans
    exact mul_le_mul
      (mul_le_mul (add_le_add (le_refl (1 : ℝ)) normV) finite_preparation_norm (norm_nonneg finitePreparation) (by norm_num))
      finite_collision_matrix_error (norm_nonneg _) (by norm_num)
  calc
    _ ≤ 9604*‖O‖*((1+(1+(3/10^17 : ℝ)))*2*(3/10^17 : ℝ)) := by
      have scaled := mul_le_mul_of_nonneg_left bound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9604) (norm_nonneg O))
      norm_num [Basis] at scaled ⊢
      exact scaled
    _ ≤ _ := by nlinarith [norm_nonneg O]

theorem original_finite_pair_energy_error (O : JointMatrix Basis) :
    |energy O (Quantum.localConjugation originalToCalculated originalToCalculated Powered.Producer.sourceReceivedPair)-
      energy O finitePair| ≤ (51/10^7 : ℝ)*‖O‖ := by
  have triangle := abs_sub_le (energy O (Quantum.localConjugation originalToCalculated originalToCalculated Powered.Producer.sourceReceivedPair))
    (energy O finiteCollisionPair) (energy O finitePair)
  nlinarith [source_collision_energy_error O,finite_coupling_energy_error O,norm_nonneg O]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
