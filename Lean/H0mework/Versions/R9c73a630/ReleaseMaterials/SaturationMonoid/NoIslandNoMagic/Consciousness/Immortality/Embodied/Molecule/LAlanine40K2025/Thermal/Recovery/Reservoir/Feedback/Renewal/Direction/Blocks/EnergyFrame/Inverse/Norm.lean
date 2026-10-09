import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.SourceEffect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Interface Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem actual_Hamiltonian_norm : ‖actualHamiltonian‖ ≤ 246 := by
  have load : ‖loadTotalHamiltonian‖ ≤ 246 := by
    have bare : ‖Powered.Dynamics.bareHamiltonian Powered.Producer.poweredTotalHamiltonian 2‖ ≤ 245 := by
      apply (norm_add_le _ _).trans
      have l := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := Fin 2)) Powered.Producer.poweredTotalHamiltonian
      have r := NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := PairController) (κ := Fin 2)) (Powered.Dynamics.controllerHamiltonian 2)
      change ‖Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ _ at l
      change ‖Matrix.kronecker (1 : Matrix PairController PairController ℂ) (Powered.Dynamics.controllerHamiltonian 2)‖ ≤ _ at r
      linarith [poweredTotalHamiltonian_norm_le,controllerHamiltonian_norm_le]
    change ‖Powered.Dynamics.bareHamiltonian Powered.Producer.poweredTotalHamiltonian 2+loadInteraction‖ ≤ _
    exact (norm_add_le _ _).trans (by linarith [actual_load_interaction_norm])
  have norm : ‖actualHamiltonian‖ = ‖loadTotalHamiltonian‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame) _
  rw [norm]
  exact load

theorem numeric_Hamiltonian_norm : ‖numericLoadHamiltonian‖ ≤ 247 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub numericLoadHamiltonian actualHamiltonian 0
  simp only [sub_zero] at triangle
  rw [norm_sub_rev numericLoadHamiltonian actualHamiltonian] at triangle
  linarith [actual_hamiltonian_distance,actual_Hamiltonian_norm]

theorem numeric_environment_norm : ‖numericEnvironmentRead‖ ≤ 12 := by
  have lambda : |numericDonorEnergy| ≤ 10 := by
    unfold numericDonorEnergy Donor.calculatedEnergy Donor.calculatedTop
    norm_num [energies]
  have bound := norm_add_le ((numericDonorEnergy : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Powered.Dynamics.controllerHamiltonian 2)
  change ‖numericEnvironmentRead‖ ≤ _ at bound
  rw [norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_eq_abs] at bound
  linarith [controllerHamiltonian_norm_le]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
