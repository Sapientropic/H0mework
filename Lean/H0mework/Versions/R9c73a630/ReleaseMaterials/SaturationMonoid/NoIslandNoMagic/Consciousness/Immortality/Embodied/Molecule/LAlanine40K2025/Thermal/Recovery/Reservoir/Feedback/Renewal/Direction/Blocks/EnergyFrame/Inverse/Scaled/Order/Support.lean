import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.DiagonalSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem numeric_PC_preserves : Preserves pcOrbit (sourcePCH E) := by
  rw [source_E_diagonal]
  have pair := pair_hamiltonian_preserves (fun i : Basis => (Donor.calculatedEnergy i : ℂ)) 1
  have interaction := interaction_preserves (fun i : Basis => (Donor.calculatedEnergy i : ℂ))
  exact preserves_add (preserves_add (preserves_tensor_left pair 1)
    (preserves_tensor_left (preserves_one pairOrbit) (Powered.Dynamics.controllerHamiltonian 2))) interaction

theorem numeric_load_preserves : Preserves pceOrbit numericLoadHamiltonian :=
  preserves_add (preserves_add (preserves_tensor_left numeric_PC_preserves 1)
    (preserves_tensor_left (preserves_one pcOrbit) (Powered.Dynamics.controllerHamiltonian 2))) source_load_interaction_preserves

theorem numeric_projector_preserves : Preserves pceOrbit numericProjector := by
  rw [projector_diagonal]
  exact preserves_diagonal pceOrbit _

theorem rational_core_preserves : Preserves pceOrbit rationalCore := by
  have env : Preserves pceOrbit (Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead) :=
    preserves_tensor_left (preserves_one pcOrbit) numericEnvironmentRead
  have pv := preserves_mul numeric_projector_preserves source_load_interaction_preserves
  have vp := preserves_mul source_load_interaction_preserves numeric_projector_preserves
  exact preserves_add (preserves_add (preserves_sub numeric_load_preserves (preserves_smul env ((sineHat : ℂ)^2)))
    (preserves_smul pv (-(sineHat : ℂ)^2-Complex.I*cosineHat*sineHat)))
    (preserves_smul vp (-(sineHat : ℂ)^2+Complex.I*cosineHat*sineHat))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
