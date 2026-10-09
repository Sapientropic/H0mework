import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bridge
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
noncomputable section

structure Material where
  parent : Residual.Material
  d3Hartree : ℝ
  occupiedHartree : ℝ
  leftResidual : ℝ
  rightResidual : ℝ

def material : Material where
  parent := Residual.material
  d3Hartree := d3HartreeEnergy
  occupiedHartree := directEnergy.re
  leftResidual := fourCenter deltaMatrix d3Matrix
  rightResidual := fourCenter occupationMatrix deltaMatrix

theorem parent_identity : material.parent = Residual.material := rfl
theorem original_D3_hartree : material.d3Hartree =
    (1 / 2 : ℝ) * ∫ z : Point × Point,
      sourceDensity z.1 * sourceDensity z.2 * kernel (z.2-z.1) := rfl
theorem occupied_hartree : material.occupiedHartree = directEnergy.re := rfl
theorem source_four_center :
    material.d3Hartree = (1 / 2 : ℝ) * fourCenter d3Matrix d3Matrix :=
  d3_hartree_source
theorem occupation_four_center :
    material.occupiedHartree = (1 / 2 : ℝ) *
      fourCenter occupationMatrix occupationMatrix := occupation_hartree_source
theorem exact_energy_residual :
    material.d3Hartree - material.occupiedHartree =
      (1 / 2 : ℝ) * (material.leftResidual + material.rightResidual) :=
  d3_occupation_hartree_residual

structure Closure : Prop where
  parent : Residual.Closure
  parentIdentity : type_of% parent_identity
  originalIntegral : type_of% original_D3_hartree
  occupiedIntegral : type_of% occupied_hartree
  originalFourCenter : type_of% source_four_center
  occupiedFourCenter : type_of% occupation_four_center
  residual : type_of% exact_energy_residual

theorem sourceGeneratedClosure : Closure :=
  ⟨Residual.sourceGeneratedClosure,parent_identity,original_D3_hartree,
    occupied_hartree,source_four_center,occupation_four_center,
    exact_energy_residual⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
