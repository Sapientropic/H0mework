import H0mework.Chemistry.LAlanineWholeCell.SourceData
import H0mework.Chemistry.LAlanineContinuousChecks.AOComplete

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellCache.Field0

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceFields

noncomputable def calculatedAO (j : LowJet) (basis : Basis) : Pair :=
  SourceRectangleChecks.calculatedAO (fullJet j) basis

theorem calculatedAO_contains (j : LowJet) (basis : Basis) (x : Point)
    (inside : InRectangle (WholeCellSource.box 0) x) :
    Holds (calculatedAO j basis) (orbital (source_terms basis) (multiindex (fullJet j)) x) := by
  rw [WholeCellSource.first_box_unchanged] at inside
  exact SourceRectangleChecks.calculatedAO_contains (fullJet j) basis x inside

end LAlanine40K2025.BasinRefinement.WholeCellCache.Field0
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
