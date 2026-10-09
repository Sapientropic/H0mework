import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Received

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open Propagation.Interface Load.Source Powered.Dynamics
open scoped Matrix
noncomputable section

theorem diagonal_pch_preserves (d : Basis → ℂ) : Preserves pcOrbit (sourcePCH (Matrix.diagonal d)) := by
  have pair := pair_hamiltonian_preserves d Thermal.Source.pairCoupling
  exact preserves_add
    (preserves_add (preserves_tensor_left pair 1)
      (preserves_tensor_left (preserves_one pairOrbit) (controllerHamiltonian 2)))
    (interaction_preserves d)

theorem diagonal_reverse_preserves (d : Basis → ℂ) : Preserves pcOrbit (Actions.reversePCH (Matrix.diagonal d)) := by
  have pair := pair_hamiltonian_preserves d Thermal.Source.pairCoupling
  exact preserves_add
    (preserves_add (preserves_tensor_left pair 1)
      (preserves_tensor_left (preserves_one pairOrbit) (controllerHamiltonian 2)))
    (preserves_neg (interaction_preserves d))

theorem numeric_pc_preserves : Preserves pcOrbit (sourcePCH E) := diagonal_pch_preserves _

theorem numeric_load_preserves : Preserves pceOrbit numericLoadHamiltonian :=
  preserves_add
    (preserves_add (preserves_tensor_left numeric_pc_preserves 1)
      (preserves_tensor_left (preserves_one pcOrbit) (controllerHamiltonian 2)))
    source_load_interaction_preserves

theorem pc_polynomial_preserves : Preserves pcOrbit Phase.pcPolynomial := flow_polynomial_preserves numeric_pc_preserves _

theorem free_polynomial_preserves : Preserves pceOrbit Phase.freePolynomial :=
  preserves_tensor_left pc_polynomial_preserves _

theorem load_polynomial_preserves : Preserves pceOrbit Actions.loadPolynomial :=
  flow_polynomial_preserves numeric_load_preserves _

theorem parent_polynomial_preserves : Preserves pceOrbit Actions.parentPolynomial :=
  preserves_tensor_left (flow_polynomial_preserves numeric_pc_preserves _) _

theorem recovery_polynomial_preserves : Preserves pceOrbit Actions.recoveryPolynomial :=
  preserves_tensor_left (flow_polynomial_preserves (diagonal_reverse_preserves _) _) _

theorem received_word_preserves : Preserves pceOrbit Actions.finiteReceivedWord :=
  preserves_mul (preserves_mul recovery_polynomial_preserves load_polynomial_preserves) parent_polynomial_preserves

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
