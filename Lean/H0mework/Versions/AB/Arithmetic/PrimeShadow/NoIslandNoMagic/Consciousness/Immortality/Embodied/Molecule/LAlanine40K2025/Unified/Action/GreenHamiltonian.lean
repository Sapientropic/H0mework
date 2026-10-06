import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenFieldEnergy
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenFieldEquation
import H0mework.Versions.AB.Physics.MotherSource.GaugeHamiltonian.Energy

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCoframeLocalDifferentiability
open StageNineCanonicalCauchyState Stage10.CanonicalGauss Stage10.TemporalGauge Stage10.GaugeHamiltonian
open MeasureTheory BasinRefinement SourceGaussianModel
noncomputable section

def generatedHamiltonianDensity (point : Point) : ℝ :=
  StaticEnergy.D3Difference (abelianPotential fieldPotential) 1 (WithLp.toLp 2 point)

theorem generated_electric_energy (point : Point) :
    lapse*squared (electric (abelianPotential fieldPotential) (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point))) =
      lapse*gradientSquare sourcePotential point := by
  rw [← electric_energy, source_abelian_energy fieldPotential _ (fieldPotential_regular.1 _)]
  have first (index : Fin 3) : fieldDirectionalDerivative fieldPotential
      (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) index.succ = spatialFirst sourcePotential index point := by
    change fieldDirectionalDerivative (fun p => sourcePotential (spatialPoint 1 p)) _ _ = _
    rw [spatial_pullback_derivative _ (sourcePotential_smooth.differentiable (by simp)), slice_source_coordinates]
  simp only [first, gradientSquare]

theorem generated_hamiltonian_density (point : Point) :
    generatedHamiltonianDensity point = -lapse*gradientSquare sourcePotential point-sourceCurrent point*sourcePotential point := by
  rw [generatedHamiltonianDensity, original_D3_generated_hamiltonian]
  simp only [fieldPotential, slice_source_coordinates]
  have electric := generated_electric_energy point
  rw [sourceCurrent_value]
  linarith

theorem generatedHamiltonian_integrable : Integrable generatedHamiltonianDensity := by
  have same : generatedHamiltonianDensity = fun point => -lapse*gradientSquare sourcePotential point-sourceCurrent point*sourcePotential point :=
    funext generated_hamiltonian_density
  rw [same]
  exact (source_gradient_integrable.const_mul _).sub source_current_potential_integrable

theorem original_D3_hamiltonian_field_energy :
    (∫ point : Point, generatedHamiltonianDensity point) = lapse*(∫ point : Point, gradientSquare sourcePotential point) := by
  simp_rw [generated_hamiltonian_density]
  rw [integral_sub (source_gradient_integrable.const_mul _) source_current_potential_integrable, integral_const_mul]
  have eliminated := original_D3_field_energy
  linarith

/-- The original complete action's D3 Legendre response reduces to the existing original Hartree consumer. -/
theorem original_D3_hamiltonian_hartree :
    (∫ point : Point, generatedHamiltonianDensity point) =
      (4*spinScale)^2/(8*Real.pi*lapse)*
        UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.d3HartreeEnergy := by
  rw [original_D3_hamiltonian_field_energy, original_D3_field_energy_hartree]

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
