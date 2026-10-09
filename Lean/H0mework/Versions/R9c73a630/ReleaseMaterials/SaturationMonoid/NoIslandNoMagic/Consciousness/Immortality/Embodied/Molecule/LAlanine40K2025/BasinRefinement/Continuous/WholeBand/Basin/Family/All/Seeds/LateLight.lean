import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A010.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A011.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A012.Flow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel WholeBandAttractor Metric Set Filter MeasureTheory
noncomputable section

def atom010Seed : Family.AttractingSeed where
  criticalPoint := Atom010.actualZero.point
  neighborhood := Atom010.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom010.actualZero Atom010.actual_zero_interior).1
  neighborhoodOpen := Atom010.attracting_open
  positiveVolume := Atom010.attracting_positive_volume
  retention := Atom010.actual_positive_retention
  convergence := Atom010.actual_convergence

def atom011Seed : Family.AttractingSeed where
  criticalPoint := Atom011.actualZero.point
  neighborhood := Atom011.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom011.actualZero Atom011.actual_zero_interior).1
  neighborhoodOpen := Atom011.attracting_open
  positiveVolume := Atom011.attracting_positive_volume
  retention := Atom011.actual_positive_retention
  convergence := Atom011.actual_convergence

def atom012Seed : Family.AttractingSeed where
  criticalPoint := Atom012.actualZero.point
  neighborhood := Atom012.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom012.actualZero Atom012.actual_zero_interior).1
  neighborhoodOpen := Atom012.attracting_open
  positiveVolume := Atom012.attracting_positive_volume
  retention := Atom012.actual_positive_retention
  convergence := Atom012.actual_convergence

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
