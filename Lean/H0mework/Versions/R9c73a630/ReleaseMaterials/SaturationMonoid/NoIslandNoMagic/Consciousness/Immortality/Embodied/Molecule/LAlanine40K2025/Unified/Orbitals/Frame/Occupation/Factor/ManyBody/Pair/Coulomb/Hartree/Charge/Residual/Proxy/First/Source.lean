import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.First.Assembly
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bridge
import Lean

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.First
open BasinRefinement SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame
open scoped Matrix BigOperators
noncomputable section

def sourceProduct (i j : Basis) : ℚ :=
  ∑ k : Basis, densityMatrix i k * Frame.First.retainedProduct k j

theorem source_product_identity (i j : Basis) :
    sourceProduct i j =
      ((Matrix.of densityMatrix : Matrix Basis Basis ℚ) *
        Matrix.of Frame.First.retainedProduct) i j := by
  simp only [sourceProduct,Matrix.mul_apply,Matrix.of_apply]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.First
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
