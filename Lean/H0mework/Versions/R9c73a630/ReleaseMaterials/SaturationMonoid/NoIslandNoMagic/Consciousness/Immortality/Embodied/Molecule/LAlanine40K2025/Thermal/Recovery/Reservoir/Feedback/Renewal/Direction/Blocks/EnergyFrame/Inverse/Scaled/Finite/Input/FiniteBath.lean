import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.FiniteGibbs
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.FiniteSystem

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def finiteBath : SystemMatrix Basis := fieldPolynomial*finiteGibbs*star fieldPolynomial

theorem original_gibbs_norm : ‖normalizedExponential transformedOriginal‖ ≤ 1 := by
  rw [← calculated_bath_exponential]
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ originalToCalculated) Thermal.Source.bathCurrent
  change ‖Quantum.conjugation originalToCalculated Thermal.Source.bathCurrent‖=‖Thermal.Source.bathCurrent‖ at same
  rw [same]
  exact state_norm_le_one _ Thermal.Source.bathCurrent_posSemidef Thermal.Source.bathCurrent_trace

theorem finite_bath_error : ‖calculatedBath-finiteBath‖ ≤ (41/10^9 : ℝ) := by
  let U := singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ)
  have near : ‖(U : SystemMatrix Basis)-fieldPolynomial‖ ≤ (2/10^14 : ℝ) := field_polynomial_error
  have normV := approximated_unitary_norm U fieldPolynomial _ near
  have action := raw_conjugation_error U fieldPolynomial (normalizedExponential transformedOriginal)
  have input := raw_input_error fieldPolynomial (normalizedExponential transformedOriginal) finiteGibbs
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Quantum.conjugation U (normalizedExponential transformedOriginal))
    (fieldPolynomial*normalizedExponential transformedOriginal*star fieldPolynomial) finiteBath
  apply triangle.trans
  apply (add_le_add action input).trans
  calc
    _ ≤ (1+(1+(2/10^14 : ℝ)))*1*(2/10^14 : ℝ)+(1+(2/10^14 : ℝ))^2*(4001/10^11 : ℝ) := by
      gcongr
      · exact original_gibbs_norm
      · exact original_finite_gibbs_error
    _ ≤ _ := by norm_num

theorem original_finite_bath_error : ‖Quantum.conjugation originalToCalculated evolvedBath-finiteBath‖ ≤ (41/10^9 : ℝ) := by
  rw [original_bath_calculated]
  exact finite_bath_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
