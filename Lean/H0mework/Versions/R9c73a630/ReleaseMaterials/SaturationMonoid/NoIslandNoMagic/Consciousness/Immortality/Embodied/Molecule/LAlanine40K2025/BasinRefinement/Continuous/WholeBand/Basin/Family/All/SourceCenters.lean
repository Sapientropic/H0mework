import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A000.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A001.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A002.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A003.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A004.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A005.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A006.Point.Data
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.SourceA007PointData
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A008.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A009.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A010.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A011.Point.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A012.Point.Data

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.CenterCalculation

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open WholeBandAttractor

noncomputable def sourceX (i : Fin 13) : Int :=
  if i=0 then Atom000.Point.rawCenter[0]! else
  if i=1 then Atom001.Point.rawCenter[0]! else
  if i=2 then Atom002.Point.rawCenter[0]! else
  if i=3 then Atom003.Point.rawCenter[0]! else
  if i=4 then Atom004.Point.rawCenter[0]! else
  if i=5 then Atom005.Point.rawCenter[0]! else
  if i=6 then Atom006.Point.rawCenter[0]! else
  if i=7 then Atom007.Point.rawCenter[0]! else
  if i=8 then Atom008.Point.rawCenter[0]! else
  if i=9 then Atom009.Point.rawCenter[0]! else
  if i=10 then Atom010.Point.rawCenter[0]! else
  if i=11 then Atom011.Point.rawCenter[0]! else
  Atom012.Point.rawCenter[0]!

theorem sourceX_eq_calculated (i : Fin 13) : sourceX i=calculatedX i := by
  fin_cases i <;> decide +kernel

theorem source_centres_separated (i j : Fin 13) (different : i ≠ j) :
    sourceX i + radiusGrid < sourceX j - radiusGrid ∨
    sourceX j + radiusGrid < sourceX i - radiusGrid := by
  rw [sourceX_eq_calculated i,sourceX_eq_calculated j]
  exact calculated_centres_separated i j different

end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
