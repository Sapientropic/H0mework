import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A003.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A004.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A005.Flow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel WholeBandAttractor Metric Set Filter MeasureTheory
noncomputable section

def atom003Seed : Family.AttractingSeed where
  criticalPoint := Atom003.actualZero.point
  neighborhood := Atom003.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom003.actualZero Atom003.actual_zero_interior).1
  neighborhoodOpen := Atom003.attracting_open
  positiveVolume := Atom003.attracting_positive_volume
  retention := Atom003.actual_positive_retention
  convergence := Atom003.actual_convergence

def atom004Seed : Family.AttractingSeed where
  criticalPoint := Atom004.actualZero.point
  neighborhood := Atom004.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom004.actualZero Atom004.actual_zero_interior).1
  neighborhoodOpen := Atom004.attracting_open
  positiveVolume := Atom004.attracting_positive_volume
  retention := Atom004.actual_positive_retention
  convergence := Atom004.actual_convergence

def atom005Seed : Family.AttractingSeed where
  criticalPoint := Atom005.actualZero.point
  neighborhood := Atom005.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom005.actualZero Atom005.actual_zero_interior).1
  neighborhoodOpen := Atom005.attracting_open
  positiveVolume := Atom005.attracting_positive_volume
  retention := Atom005.actual_positive_retention
  convergence := Atom005.actual_convergence

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
