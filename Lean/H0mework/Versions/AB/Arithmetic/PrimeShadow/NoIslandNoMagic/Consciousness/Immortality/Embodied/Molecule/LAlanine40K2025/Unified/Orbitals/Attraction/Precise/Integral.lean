import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.SourceData
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coulomb

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData SourceCoulomb
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
noncomputable section

/-- The original target-frame geometry uses binary rational coordinates;
    Root156's picobohr ledger position is a separate rounded readout. -/
def aoIntegral (i j : Basis) : ℝ :=
  ∑ a : Fin 13, -Nuclear.nuclearCharge a *
    ∫ x : Point, ao i x * ao j x *
      kernel (x - fun k => (nucleus a k : ℝ))

def totalIntegral : ℝ :=
  ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * aoIntegral i j

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
