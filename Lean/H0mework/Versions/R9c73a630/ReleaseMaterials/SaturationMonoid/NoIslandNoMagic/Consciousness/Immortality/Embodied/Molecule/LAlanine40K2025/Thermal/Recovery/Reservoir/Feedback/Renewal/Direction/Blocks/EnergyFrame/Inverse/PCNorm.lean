import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Centered

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Interface Load.Source Powered.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem numeric_pair_norm : ‖pairHamiltonian E‖ ≤ 39 := by
  have free : ‖Thermal.Dynamics.freePairH E‖ ≤ 38 := by
    apply (norm_add_le _ _).trans
    have left := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := Basis) (κ := Basis)) E
    have right := NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := Basis) (κ := Basis)) E
    change ‖Matrix.kronecker E (1 : Matrix Basis Basis ℂ)‖ ≤ _ at left
    change ‖Matrix.kronecker (1 : Matrix Basis Basis ℂ) E‖ ≤ _ at right
    linarith [diagonal_norm]
  change ‖Thermal.Dynamics.freePairH E+(1 : ℂ) • swapOperator‖ ≤ _
  rw [one_smul]
  have bound := norm_add_le (Thermal.Dynamics.freePairH E) (swapOperator : JointMatrix Basis)
  rw [swap_norm] at bound
  linarith

theorem numeric_bare_PC_norm : ‖bareHamiltonian (pairHamiltonian E) 2‖ ≤ 41 := by
  apply (norm_add_le _ _).trans
  have left := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := Basis × Basis) (κ := Fin 2)) (pairHamiltonian E)
  have right := NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := Basis × Basis) (κ := Fin 2)) (Powered.Dynamics.controllerHamiltonian 2)
  change ‖Matrix.kronecker (pairHamiltonian E) (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ _ at left
  change ‖Matrix.kronecker (1 : JointMatrix Basis) (Powered.Dynamics.controllerHamiltonian 2)‖ ≤ _ at right
  linarith [numeric_pair_norm,controllerHamiltonian_norm_le]

theorem numeric_PC_norm : ‖sourcePCH E‖ ≤ 89 := by
  have bound := norm_add_le (bareHamiltonian (pairHamiltonian E) 2) (interaction E)
  exact bound.trans (by linarith [numeric_bare_PC_norm,numeric_interaction_norm])

theorem original_PC_norm : ‖Powered.Producer.poweredTotalHamiltonian‖ ≤ 90 := by
  have bound := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian) (sourcePCH E) 0
  simp only [sub_zero] at bound
  have norm : ‖Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian‖=
      ‖Powered.Producer.poweredTotalHamiltonian‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ
        (Matrix PairController PairController ℂ) installedPCFrame) _
  rw [norm] at bound
  have delta := actual_powered_Hamiltonian_error
  change ‖Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian-sourcePCH E‖ ≤ _ at delta
  linarith [numeric_PC_norm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
