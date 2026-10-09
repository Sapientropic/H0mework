import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.First.Assembly

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Second
open BasinRefinement SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame
open scoped Matrix BigOperators
noncomputable section

def sourceProduct (i j : Basis) : ℚ :=
  ∑ k : Basis, Frame.First.retainedProduct k i * Proxy.First.retainedProduct k j

theorem source_product_identity (i j : Basis) :
    sourceProduct i j =
      ((Matrix.of Frame.First.retainedProduct).transpose *
        Matrix.of Proxy.First.retainedProduct) i j := by
  simp only [sourceProduct,Matrix.mul_apply,Matrix.of_apply,Matrix.transpose_apply]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Second
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
