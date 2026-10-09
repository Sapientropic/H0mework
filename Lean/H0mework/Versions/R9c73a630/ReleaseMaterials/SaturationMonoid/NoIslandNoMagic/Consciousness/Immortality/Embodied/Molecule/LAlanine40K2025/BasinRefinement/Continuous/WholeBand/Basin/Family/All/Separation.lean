import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Seeds
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Geometry

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel SourceExponential WholeBandAttractor Set Metric Function
noncomputable section

theorem source_critical_distinct (i j : Fin 13) (different : i ≠ j) :
    (sourceSeed i).criticalPoint ≠ (sourceSeed j).criticalPoint := by
  rcases source_centre_gap i j different with h | h
  · exact Family.critical_distinct_of_separated_boxes _ _ _ _ _ _
      (source_zero_inside i) (source_zero_inside j)
      (by norm_num [sourceRadius]) (by norm_num [sourceRadius]) h
  · intro same
    exact Family.critical_distinct_of_separated_boxes _ _ _ _ _ _
      (source_zero_inside j) (source_zero_inside i)
      (by norm_num [sourceRadius]) (by norm_num [sourceRadius]) h same.symm

theorem source_basins_disjoint :
    Pairwise (Disjoint on fun i : Fin 13 => Family.basin (sourceSeed i)) := by
  intro i j different
  exact Family.basins_disjoint_of_critical_ne (sourceSeed i) (sourceSeed j)
    (source_critical_distinct i j different)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
