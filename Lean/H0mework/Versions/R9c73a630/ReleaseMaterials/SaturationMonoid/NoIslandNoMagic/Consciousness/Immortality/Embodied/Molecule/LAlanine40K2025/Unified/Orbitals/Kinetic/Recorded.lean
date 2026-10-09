import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Address

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Kinetic
open BasinRefinement SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
noncomputable section

/-- Upper-triangle address of the ordered basis pair. -/
def kineticPairIndex (b c : Basis) : Nat :=
  b.val * (197 - b.val) / 2 + (c.val - b.val)

/-- The kinetic integral recorded in the target ledger for this AO pair,
    in picohartree scaled to hartree.  Lower-triangular queries consume the
    same canonical row through the pair order. -/
def recordedKinetic (b c : Basis) : ℚ :=
  if b.val ≤ c.val then
    (((targetAORow (kineticPairIndex b c))[5]! : ℤ) : ℚ) / 10^12
  else
    (((targetAORow (kineticPairIndex c b))[5]! : ℤ) : ℚ) / 10^12

end
end LAlanine40K2025.UnifiedOrbitals.Kinetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
