import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.NuclearAttractionGreen
import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.NuclearPairGreen
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenHamiltonian

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.PreciseNuclear
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel WholeBandBasin.Family.All.Nuclear
noncomputable section

/-- The generated electron field Hamiltonian, its nuclear coupling, and the finite nuclear pairs. -/
def electrostaticEnergy : ℝ :=
  (∫ point : Point, GreenSource.generatedHamiltonianDensity point)+electronNuclearEnergy+repulsion 1

theorem original_full_target_coulomb_energy :
    electrostaticEnergy = (4*spinScale)^2/(8*Real.pi*lapse)*
      (UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.d3HartreeEnergy+
        UnifiedOrbitals.Attraction.Precise.totalIntegral+PreciseTarget.totalRepulsion) := by
  rw [electrostaticEnergy, GreenSource.original_D3_hamiltonian_hartree, original_electron_nuclear_energy,
    original_repulsion_green 1 zero_lt_one]
  simp only [GreenSource.greenCoefficient, mul_one]
  ring

end
end LAlanine40K2025.UnifiedAction.PreciseNuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
