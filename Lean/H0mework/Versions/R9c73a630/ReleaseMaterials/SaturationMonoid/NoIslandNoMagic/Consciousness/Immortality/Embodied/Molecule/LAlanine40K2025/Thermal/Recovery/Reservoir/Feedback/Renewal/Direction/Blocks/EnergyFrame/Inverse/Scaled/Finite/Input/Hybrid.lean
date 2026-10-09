import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.FiniteBath

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def hybridBath : SystemMatrix Basis := Quantum.conjugation
  (singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ)) spectralBath

theorem calculated_base_lawful : calculatedBaseSystem.PosSemidef ∧ calculatedBaseSystem.trace=1 :=
  ⟨Quantum.conjugation_posSemidef (star actualUnitary) _ base_system_lawful.1,
    (Quantum.conjugation_trace (star actualUnitary) baseSystem).trans base_system_lawful.2⟩

theorem calculated_system_lawful : calculatedSystem.PosSemidef ∧ calculatedSystem.trace=1 := by
  rw [calculated_system_word]
  exact ⟨Quantum.conjugation_posSemidef _ _ calculated_base_lawful.1,
    (Quantum.conjugation_trace calculatedSystemWord calculatedBaseSystem).trans calculated_base_lawful.2⟩

theorem hybrid_bath_lawful : hybridBath.PosSemidef ∧ hybridBath.trace=1 :=
  ⟨Quantum.conjugation_posSemidef _ _ reference_gibbs_lawful.1,
    (Quantum.conjugation_trace _ spectralBath).trans reference_gibbs_lawful.2⟩

theorem calculated_bath_lawful : calculatedBath.PosSemidef ∧ calculatedBath.trace=1 := by
  rw [← original_bath_calculated,evolvedBath]
  exact ⟨Quantum.conjugation_posSemidef _ _ (Quantum.conjugation_posSemidef _ _ Thermal.Source.bathCurrent_posSemidef),
    (Quantum.conjugation_trace _ _).trans ((Quantum.conjugation_trace _ _).trans Thermal.Source.bathCurrent_trace)⟩

theorem hybrid_bath_error : ‖calculatedBath-hybridBath‖ ≤ (4/10^8 : ℝ) := by
  change ‖Quantum.conjugation _ (normalizedExponential transformedOriginal)-Quantum.conjugation _ spectralBath‖ ≤ _
  rw [← map_sub]
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ)))
    (normalizedExponential transformedOriginal-spectralBath)
  change ‖Quantum.conjugation _ _‖=_ at same
  rw [same]
  exact original_spectral_bath_error

theorem hybrid_finite_bath_error : ‖hybridBath-finiteBath‖ ≤ (5/10^12 : ℝ) := by
  let U := singleUnitary calculatedFieldHamiltonian calculated_field_hermitian (nativeClockStep : ℝ)
  have near : ‖(U : SystemMatrix Basis)-fieldPolynomial‖ ≤ (2/10^14 : ℝ) := field_polynomial_error
  have normV := approximated_unitary_norm U fieldPolynomial _ near
  have action := raw_conjugation_error U fieldPolynomial spectralBath
  have input := raw_input_error fieldPolynomial spectralBath finiteGibbs
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Quantum.conjugation U spectralBath)
    (fieldPolynomial*spectralBath*star fieldPolynomial) finiteBath
  apply triangle.trans
  apply (add_le_add action input).trans
  calc
    _ ≤ (1+(1+(2/10^14 : ℝ)))*1*(2/10^14 : ℝ)+(1+(2/10^14 : ℝ))^2*(4/10^12 : ℝ) := by
      gcongr
      · exact reference_gibbs_norm
      · exact spectral_finite_gibbs_error
    _ ≤ _ := by norm_num

theorem finite_system_positive : finiteSystem.PosSemidef := by
  have raw : rawBaseSystem.PosSemidef := by
    have p := base_system_lawful.1.mul_mul_conjTranspose_same (star Q)
    simpa only [rawBaseSystem,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using p
  exact raw.mul_mul_conjTranspose_same finiteSystemWord

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
