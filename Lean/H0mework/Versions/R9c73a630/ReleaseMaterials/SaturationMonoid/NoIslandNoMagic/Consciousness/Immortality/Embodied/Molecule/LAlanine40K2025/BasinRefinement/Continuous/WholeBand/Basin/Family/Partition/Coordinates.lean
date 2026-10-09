import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.Cells
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
open SourceGaussianModel WholeBandBasin Set
noncomputable section

def residual : Set Point :=
  (Family.atom006Basin ∪ WholeBandBasin.basin ∪ Family.atom009Basin)ᶜ

theorem zone_zero : zone 0=Family.atom006Basin := by
  classical
  ext x
  change zoneIndex x=0 ↔ x∈Family.atom006Basin
  by_cases h6 : x∈Family.atom006Basin
  · simp [zoneIndex,h6]
  · by_cases h7 : x∈WholeBandBasin.basin
    · simp [zoneIndex,h6,h7]
    · by_cases h9 : x∈Family.atom009Basin <;> simp [zoneIndex,h6,h7,h9]

theorem zone_one : zone 1=WholeBandBasin.basin := by
  classical
  ext x
  change zoneIndex x=1 ↔ x∈WholeBandBasin.basin
  by_cases h6 : x∈Family.atom006Basin
  · have hnot7 : x∉WholeBandBasin.basin :=
      fun h7 => Set.disjoint_left.mp Family.original_basins_disjoint h6 h7
    simp [zoneIndex,h6,hnot7]
  · by_cases h7 : x∈WholeBandBasin.basin
    · simp [zoneIndex,h6,h7]
    · by_cases h9 : x∈Family.atom009Basin <;> simp [zoneIndex,h6,h7,h9]

theorem zone_two : zone 2=Family.atom009Basin := by
  classical
  ext x
  change zoneIndex x=2 ↔ x∈Family.atom009Basin
  by_cases h6 : x∈Family.atom006Basin
  · have hnot9 : x∉Family.atom009Basin :=
      fun h9 => Set.disjoint_left.mp Family.original_basins_6_9_disjoint h6 h9
    simp [zoneIndex,h6,hnot9]
  · by_cases h7 : x∈WholeBandBasin.basin
    · have hnot9 : x∉Family.atom009Basin :=
        fun h9 => Set.disjoint_left.mp Family.original_basins_7_9_disjoint h7 h9
      simp [zoneIndex,h6,h7,hnot9]
    · by_cases h9 : x∈Family.atom009Basin <;> simp [zoneIndex,h6,h7,h9]

theorem zone_three : zone 3=residual := by
  classical
  ext x
  change zoneIndex x=3 ↔ x∈residual
  by_cases h6 : x∈Family.atom006Basin
  · simp [zoneIndex,residual,h6]
  · by_cases h7 : x∈WholeBandBasin.basin
    · simp [zoneIndex,residual,h6,h7]
    · by_cases h9 : x∈Family.atom009Basin <;>
        simp [zoneIndex,residual,h6,h7,h9]

theorem original_cell_6_7 : pairCell (0,1)=Family.crossRegion := by
  rw [pairCell_prod,zone_zero,zone_one]
  rfl

theorem original_cell_6_9 :
    pairCell (0,2)=Family.pairRegion Family.atom006Seed Family.atom009Seed := by
  rw [pairCell_prod,zone_zero,zone_two]
  rfl

theorem original_cell_7_9 :
    pairCell (1,2)=Family.pairRegion Family.atom007Seed Family.atom009Seed := by
  rw [pairCell_prod,zone_one,zone_two,← Family.atom007_basin_same_source]
  rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
