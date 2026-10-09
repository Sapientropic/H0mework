import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OldCells
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Fifth.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
noncomputable section

structure Material where
  parent : Family.Fifth.Material
  seeds : Fin 13 → Family.AttractingSeed
  cells : Option (Fin 13) × Option (Fin 13) → ℝ
  residual : Set Point

def material : Material where
  parent := Family.Fifth.material
  seeds := sourceSeed
  cells := cellEnergy
  residual := region none

theorem parent_same_source : material.parent=Family.Fifth.material := rfl
theorem seeds_same_source (i : Fin 13) : material.seeds i=sourceSeed i := rfl
theorem cells_same_source (ij : Option (Fin 13) × Option (Fin 13)) :
    material.cells ij=cellEnergy ij := rfl
theorem residual_same_source : material.residual=(⋃ i : Fin 13, sourceBasin i)ᶜ :=
  original_residual

theorem old_four_seeds_same_source :
    sourceSeed 6=Family.atom006Seed ∧
    sourceSeed 7=Family.atom007Seed ∧
    sourceSeed 8=Family.atom008Seed ∧
    sourceSeed 9=Family.atom009Seed := ⟨rfl,rfl,rfl,rfl⟩

structure Closure : Prop where
  parent : Family.Fifth.Closure
  parentIdentity : type_of% parent_same_source
  seedIdentity : type_of% seeds_same_source
  cellIdentity : type_of% cells_same_source
  residualIdentity : type_of% residual_same_source
  oldSeedIdentity : type_of% old_four_seeds_same_source
  oldAtomicCells : type_of% old_atomic_cell_same_source
  allSourceZeroInside : type_of% source_zero_inside
  rawCentresSeparated : type_of% source_centres_separated
  allCriticalDistinct : type_of% source_critical_distinct
  allBasinsDisjoint : type_of% source_basins_disjoint
  allBasinsOpen : type_of% all_basins_open
  allBasinsPositive : type_of% all_basins_positive
  allBasinPatches : type_of% all_basins_patch_cover
  allOriginalRegions : type_of% original_region
  originalResidual : type_of% original_residual
  allRegionsMeasurable : type_of% all_regions_measurable
  allPairCellsMeasurable : type_of% all_pair_cells_measurable
  allPairCellsDisjoint : type_of% all_pair_cells_disjoint
  allPairCellsCover : type_of% all_pair_cells_cover
  allPairCellsNonempty : type_of% every_original_pair_cell_nonempty
  nonnegative : type_of% all_cell_energy_nonnegative
  symmetric : type_of% all_cell_energy_symmetric
  fullEnergy : type_of% all_energy_exact
  originalAO : type_of% all_original_ao_energy
  allIntra : type_of% every_original_intra_energy
  allAtomPairs : type_of% every_original_pair_energy
  allPatchLimits : type_of% every_original_pair_patch_limit

theorem sourceGeneratedClosure : Closure :=
  ⟨Family.Fifth.sourceGeneratedClosure,
    parent_same_source,seeds_same_source,cells_same_source,
    residual_same_source,old_four_seeds_same_source,
    old_atomic_cell_same_source,
    source_zero_inside,source_centres_separated,source_critical_distinct,
    source_basins_disjoint,all_basins_open,all_basins_positive,
    all_basins_patch_cover,original_region,original_residual,
    all_regions_measurable,all_pair_cells_measurable,
    all_pair_cells_disjoint,all_pair_cells_cover,
    every_original_pair_cell_nonempty,
    all_cell_energy_nonnegative,all_cell_energy_symmetric,
    all_energy_exact,all_original_ao_energy,
    every_original_intra_energy,every_original_pair_energy,
    every_original_pair_patch_limit⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
