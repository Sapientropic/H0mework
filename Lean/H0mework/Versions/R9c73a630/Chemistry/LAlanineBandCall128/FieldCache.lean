import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCall128.FieldGroups
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCall128.FieldOrbitals
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCache.Assembly

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Call128

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangleChecks SourceFields

open WholeBandCache

theorem all_groups (g : Group) : GroupComputed localBox localReductions material g := by
  fin_cases g
  closeWholeBandRows 94 "group"

theorem all_orbitals (b : Basis) : OrbitalComputed localBox material b := by
  fin_cases b
  closeWholeBandRows 98 "orbital"

theorem actual_orbitals (j : LowJet) (b : Basis) (x : Point)
    (inside : InRectangle (WholeBandSource.callBox 128) x) :
    Holds (calculatedAO material j b) (orbital (source_terms b) (multiindex (fullJet j)) x) := by
  apply calculatedAO_contains all_groups all_orbitals
  rw [box_is_original]
  exact inside

end LAlanine40K2025.BasinRefinement.WholeBandCell2.Call128
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
