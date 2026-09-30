import H0mework.Chemistry.LAlanineBandCall005.FieldGroups
import H0mework.Chemistry.LAlanineBandCall005.FieldOrbitals
import H0mework.Chemistry.LAlanineBandCache.Assembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCache.Call5

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangleChecks SourceFields

theorem all_groups (g : Group) : GroupComputed localBox localReductions material g := by
  fin_cases g
  closeWholeBandRows 94 "group"

theorem all_orbitals (b : Basis) : OrbitalComputed localBox material b := by
  fin_cases b
  closeWholeBandRows 98 "orbital"

theorem actual_orbitals (j : LowJet) (b : Basis) (x : Point)
    (inside : InRectangle (WholeBandSource.callBox 5) x) :
    Holds (calculatedAO material j b) (orbital (source_terms b) (multiindex (fullJet j)) x) := by
  apply calculatedAO_contains all_groups all_orbitals
  rw [box_is_original]
  exact inside

end LAlanine40K2025.BasinRefinement.WholeBandCache.Call5
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
