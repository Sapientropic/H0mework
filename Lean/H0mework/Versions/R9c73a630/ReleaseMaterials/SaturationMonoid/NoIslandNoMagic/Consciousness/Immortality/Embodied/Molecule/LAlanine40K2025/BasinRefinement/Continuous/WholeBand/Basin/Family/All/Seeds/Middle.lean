import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A006.Flow
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.SourceA007Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A008.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Attractor.Source.A009.Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Cover

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource Set Filter Metric MeasureTheory
open WholeBandAttractor
noncomputable section

def atom006Seed : AttractingSeed where
  criticalPoint := Atom006.actualZero.point
  neighborhood := Atom006.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom006.actualZero Atom006.actual_zero_interior).1
  neighborhoodOpen := Atom006.attracting_open
  positiveVolume := Atom006.attracting_positive_volume
  retention := Atom006.actual_positive_retention
  convergence := Atom006.actual_convergence

def atom007Seed : AttractingSeed where
  criticalPoint := Atom007.actualZero.point
  neighborhood := Atom007.attractingNeighborhood
  criticalInside := WholeBandBasin.critical_inside_neighborhood
  neighborhoodOpen := Atom007.attracting_open
  positiveVolume := Atom007.attracting_positive_volume
  retention := Atom007.actual_positive_retention
  convergence := Atom007.actual_convergence

def atom008Seed : AttractingSeed where
  criticalPoint := Atom008.actualZero.point
  neighborhood := Atom008.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom008.actualZero Atom008.actual_zero_interior).1
  neighborhoodOpen := Atom008.attracting_open
  positiveVolume := Atom008.attracting_positive_volume
  retention := Atom008.actual_positive_retention
  convergence := Atom008.actual_convergence

def atom009Seed : AttractingSeed where
  criticalPoint := Atom009.actualZero.point
  neighborhood := Atom009.attractingNeighborhood
  criticalInside := Metric.mem_ball_self
    (Attractor.neighborhood_geometry Atom009.actualZero Atom009.actual_zero_interior).1
  neighborhoodOpen := Atom009.attracting_open
  positiveVolume := Atom009.attracting_positive_volume
  retention := Atom009.actual_positive_retention
  convergence := Atom009.actual_convergence

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
