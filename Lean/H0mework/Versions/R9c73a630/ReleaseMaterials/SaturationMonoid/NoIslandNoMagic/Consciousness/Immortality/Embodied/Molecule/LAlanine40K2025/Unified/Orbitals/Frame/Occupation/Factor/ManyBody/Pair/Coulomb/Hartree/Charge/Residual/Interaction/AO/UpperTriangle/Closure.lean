import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : GaussianPair.Material
  upperJ : Matrix Basis Basis ℝ
  upperHartree : ℝ

def material : Material where
  parent := GaussianPair.material
  upperJ := Matrix.of sourceJUpper
  upperHartree := hartreeUpper

theorem parent_identity : material.parent = GaussianPair.material := rfl

theorem potential_exact (i j : Basis) :
    material.parent.parent.jPotential i j = material.upperJ i j :=
  sourceJ_eq_upper i j

theorem hartree_exact :
    material.parent.parent.hartree = material.upperHartree :=
  original_hartree_eq_upper

structure Closure : Prop where
  parent : GaussianPair.Closure
  sourcePotential : type_of% sourceJ_eq_upper
  sourceHartree : type_of% original_hartree_eq_upper
  parentIdentity : type_of% parent_identity
  potential : type_of% potential_exact
  hartree : type_of% hartree_exact

theorem sourceGeneratedClosure : Closure :=
  ⟨GaussianPair.sourceGeneratedClosure,sourceJ_eq_upper,original_hartree_eq_upper,
    parent_identity,potential_exact,hartree_exact⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
