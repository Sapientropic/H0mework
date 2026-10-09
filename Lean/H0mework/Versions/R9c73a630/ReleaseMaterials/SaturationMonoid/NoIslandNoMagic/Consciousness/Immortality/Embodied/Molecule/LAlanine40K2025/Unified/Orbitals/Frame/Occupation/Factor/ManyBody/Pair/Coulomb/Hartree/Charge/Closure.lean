import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient MeasureTheory
noncomputable section

structure Material where
  parent : Hartree.Material
  projected : Point → ℝ
  residual : Point → ℝ

def material : Material where
  parent := Hartree.material
  projected := projectedDensity
  residual := densityResidual

theorem parent_identity : material.parent = Hartree.material := rfl
theorem projected_from_occupied (x : Point) :
    material.projected x = 2 * ‖occupiedVector x‖^2 := projected_density_norm x
theorem original_D3_decomposition (x : Point) :
    sourceDensity x = material.projected x + material.residual x := by
  simp [material,densityResidual]
theorem projected_integrable : Integrable material.projected := projected_density_integrable
theorem residual_integrable : Integrable material.residual := density_residual_integrable
theorem projected_electron_count :
    (∫ x : Point, material.projected x) = 48 := projected_charge
theorem original_D3_total_residual :
    |∫ x : Point, material.residual x| ≤ (1 / 10^9 : ℝ) :=
  original_D3_charge_residual

structure Closure : Prop where
  parent : Hartree.Closure
  parentIdentity : type_of% parent_identity
  occupation : type_of% projected_from_occupied
  sourceD3 : type_of% original_D3_decomposition
  projectedIntegrable : Integrable material.projected
  residualIntegrable : Integrable material.residual
  electronCount : type_of% projected_electron_count
  residualBound : type_of% original_D3_total_residual

theorem sourceGeneratedClosure : Closure :=
  ⟨Hartree.sourceGeneratedClosure,parent_identity,projected_from_occupied,
    original_D3_decomposition,projected_integrable,residual_integrable,
    projected_electron_count,original_D3_total_residual⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
