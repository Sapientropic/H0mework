import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A000.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A001.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A002.Flow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel WholeBandAttractor Metric Set Filter MeasureTheory
noncomputable section

def atom000Seed : Family.AttractingSeed where
  criticalPoint := Atom000.actualZero.point
  neighborhood := Atom000.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom000.actualZero Atom000.actual_zero_interior).1
  neighborhoodOpen := Atom000.attracting_open
  positiveVolume := Atom000.attracting_positive_volume
  retention := Atom000.actual_positive_retention
  convergence := Atom000.actual_convergence

def atom001Seed : Family.AttractingSeed where
  criticalPoint := Atom001.actualZero.point
  neighborhood := Atom001.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom001.actualZero Atom001.actual_zero_interior).1
  neighborhoodOpen := Atom001.attracting_open
  positiveVolume := Atom001.attracting_positive_volume
  retention := Atom001.actual_positive_retention
  convergence := Atom001.actual_convergence

def atom002Seed : Family.AttractingSeed where
  criticalPoint := Atom002.actualZero.point
  neighborhood := Atom002.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom002.actualZero Atom002.actual_zero_interior).1
  neighborhoodOpen := Atom002.attracting_open
  positiveVolume := Atom002.attracting_positive_volume
  retention := Atom002.actual_positive_retention
  convergence := Atom002.actual_convergence

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
