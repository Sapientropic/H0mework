import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Product
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.PhaseMatrices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def calculatedSystemWord : Matrix.unitaryGroup Basis ℂ :=
  singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ)*
    singleUnitary transformedOriginal transformed_hermitian systemTime

def finiteSystemWord : SystemMatrix Basis := fieldPolynomial*activePolynomial
def finiteSystem : SystemMatrix Basis := finiteSystemWord*rawBaseSystem*star finiteSystemWord

theorem calculated_system_word : calculatedSystem=Quantum.conjugation calculatedSystemWord calculatedBaseSystem := by
  rw [calculatedSystem,Environment.conjugation_comp]
  rfl

theorem finite_system_word_error : ‖(calculatedSystemWord : SystemMatrix Basis)-finiteSystemWord‖ ≤ (6/10^11 : ℝ) := by
  exact (approximated_product_error
    (singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ))
    (singleUnitary transformedOriginal transformed_hermitian systemTime)
    fieldPolynomial activePolynomial (2/10^14) (5/10^11) field_polynomial_error active_polynomial_error).trans (by norm_num)

theorem calculated_base_norm : ‖calculatedBaseSystem‖ ≤ 1 := by
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (star actualUnitary)) baseSystem
  change ‖calculatedBaseSystem‖=‖baseSystem‖ at same
  rw [same]
  exact state_norm_le_one baseSystem base_system_lawful.1 base_system_lawful.2

theorem finite_system_error : ‖calculatedSystem-finiteSystem‖ ≤ (13/10^11 : ℝ) := by
  rw [calculated_system_word,finiteSystem]
  have normV := approximated_unitary_norm calculatedSystemWord finiteSystemWord _ finite_system_word_error
  have action := raw_conjugation_error calculatedSystemWord finiteSystemWord calculatedBaseSystem
  have input := raw_input_error finiteSystemWord calculatedBaseSystem rawBaseSystem
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Quantum.conjugation calculatedSystemWord calculatedBaseSystem)
    (finiteSystemWord*calculatedBaseSystem*star finiteSystemWord) (finiteSystemWord*rawBaseSystem*star finiteSystemWord)
  apply triangle.trans
  apply (add_le_add action input).trans
  calc
    _ ≤ (1+(1+(6/10^11 : ℝ)))*1*(6/10^11 : ℝ)+(1+(6/10^11 : ℝ))^2*(7/10^13 : ℝ) := by
      gcongr
      · exact calculated_base_norm
      · exact finite_system_word_error
      · exact raw_base_system_error
    _ ≤ _ := by norm_num

theorem original_finite_system_error : ‖Quantum.conjugation originalToCalculated evolvedSystem-finiteSystem‖ ≤ (13/10^11 : ℝ) := by
  rw [original_system_calculated]
  exact finite_system_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
