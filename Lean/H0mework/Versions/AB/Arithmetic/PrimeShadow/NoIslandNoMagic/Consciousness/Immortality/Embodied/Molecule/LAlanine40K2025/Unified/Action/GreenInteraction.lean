import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Interaction
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenPotential
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bridge

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel SourceFiniteData SourceCoulomb ContinuousGradient
open UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual
noncomputable section

theorem original_D3_interaction_energy :
    interactionEnergy sourceCurrent =
      (4*spinScale)^2/(8*Real.pi*lapse)*Interaction.d3HartreeEnergy := by
  unfold interactionEnergy Interaction.d3HartreeEnergy
  have same (points : Point × Point) :
      sourceCurrent points.1*sourceCurrent points.2*green (points.2-points.1) =
      ((4*spinScale)^2/(8*Real.pi*lapse))*(sourceDensity points.1*sourceDensity points.2*kernel (points.2-points.1)) := by
    rw [sourceCurrent_value, sourceCurrent_value, green_kernel]
    ring
  simp_rw [same]
  rw [integral_const_mul]
  ring

theorem original_D3_potential_energy :
    -(1/2 : ℝ)*(∫ point : Point, sourceCurrent point*sourcePotential point) =
      (4*spinScale)^2/(8*Real.pi*lapse)*Interaction.d3HartreeEnergy := by
  unfold sourcePotential
  rw [← interaction_potential sourceCurrent sourceCurrent_integrable _ sourceCurrent_bound]
  exact original_D3_interaction_energy

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
