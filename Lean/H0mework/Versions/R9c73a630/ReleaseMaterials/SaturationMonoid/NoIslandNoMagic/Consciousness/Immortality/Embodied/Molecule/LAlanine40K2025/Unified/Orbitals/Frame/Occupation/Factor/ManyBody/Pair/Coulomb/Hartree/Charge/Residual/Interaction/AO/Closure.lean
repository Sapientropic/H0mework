import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
noncomputable section

structure Material where
  parent : Proxy.Final.Material
  densityAO : Matrix Basis Basis ℝ
  jPotential : Matrix Basis Basis ℝ
  hartree : ℝ

def material : Material where
  parent := Proxy.Final.material
  densityAO := Proxy.Correction.d3AO
  jPotential := Matrix.of sourceJ
  hartree := Interaction.d3HartreeEnergy

theorem parent_identity : material.parent = Proxy.Final.material := rfl
theorem original_density (x : Point) :
    densityFrom material.densityAO x = sourceDensity x := source_density_ao x
theorem source_potential (i j : Basis) :
    material.jPotential i j =
      ∑ k : Basis, ∑ l : Basis,
        material.densityAO k l * electronRepulsion i j k l := by
  simpa only [material,Matrix.of_apply] using sourceJ_physical_order i j
theorem source_potential_symmetric (i j : Basis) :
    material.jPotential i j = material.jPotential j i := sourceJ_symmetric i j
theorem original_hartree_source :
    material.hartree = (1 / 2 : ℝ) *
      ∑ i : Basis, ∑ j : Basis,
        material.densityAO i j * material.jPotential i j :=
  original_D3_hartree_sourceJ

structure Closure : Prop where
  parent : Proxy.Final.Closure
  parentIdentity : type_of% parent_identity
  density : type_of% original_density
  potential : type_of% source_potential
  symmetry : type_of% source_potential_symmetric
  energy : type_of% original_hartree_source

theorem sourceGeneratedClosure : Closure :=
  ⟨Proxy.Final.sourceGeneratedClosure,parent_identity,original_density,
    source_potential,source_potential_symmetric,original_hartree_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
