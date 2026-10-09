import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Fourth
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.Finite
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
open SourceGaussianModel WholeBandBasin Set MeasureTheory Function
noncomputable section

def zoneIndex (x : Point) : Fin 5 := by
  classical
  exact if x ∈ Family.atom006Basin then 0 else
    if x ∈ WholeBandBasin.basin then 1 else
    if x ∈ Family.atom008Basin then 2 else
    if x ∈ Family.atom009Basin then 3 else 4

def zone (i : Fin 5) : Set Point := Partition.Finite.region zoneIndex i
def pairCell (i : Fin 5 × Fin 5) : Set (Point × Point) :=
  Partition.Finite.pairCell zoneIndex i
def cellEnergy (i : Fin 5 × Fin 5) : ℝ := Partition.Finite.cellEnergy zoneIndex i
def residual : Set Point :=
  (Family.atom006Basin ∪ WholeBandBasin.basin ∪ Family.atom008Basin ∪ Family.atom009Basin)ᶜ

theorem zoneIndex_measurable : Measurable zoneIndex := by
  classical
  unfold zoneIndex
  exact Measurable.ite Family.atom006_basin_open.measurableSet measurable_const
    (Measurable.ite WholeBandBasin.basin_measurable measurable_const
      (Measurable.ite Family.atom008_basin_open.measurableSet measurable_const
        (Measurable.ite Family.atom009_basin_open.measurableSet measurable_const measurable_const)))

theorem zone_measurable (i : Fin 5) : MeasurableSet (zone i) :=
  zoneIndex_measurable (measurableSet_singleton i)

theorem zone_zero : zone 0=Family.atom006Basin := by
  classical
  ext x
  change zoneIndex x=0 ↔ x∈Family.atom006Basin
  by_cases h6 : x∈Family.atom006Basin
  · simp [zoneIndex,h6]
  · by_cases h7 : x∈WholeBandBasin.basin
    · simp [zoneIndex,h6,h7]
    · by_cases h8 : x∈Family.atom008Basin
      · simp [zoneIndex,h6,h7,h8]
      · by_cases h9 : x∈Family.atom009Basin <;> simp [zoneIndex,h6,h7,h8,h9]

theorem zone_one : zone 1=WholeBandBasin.basin := by
  classical
  ext x
  change zoneIndex x=1 ↔ x∈WholeBandBasin.basin
  by_cases h6 : x∈Family.atom006Basin
  · have hn7 : x∉WholeBandBasin.basin :=
      fun h7 => Set.disjoint_left.mp Family.original_basins_disjoint h6 h7
    simp [zoneIndex,h6,hn7]
  · by_cases h7 : x∈WholeBandBasin.basin
    · simp [zoneIndex,h6,h7]
    · by_cases h8 : x∈Family.atom008Basin
      · simp [zoneIndex,h6,h7,h8]
      · by_cases h9 : x∈Family.atom009Basin <;> simp [zoneIndex,h6,h7,h8,h9]

theorem zone_two : zone 2=Family.atom008Basin := by
  classical
  ext x
  change zoneIndex x=2 ↔ x∈Family.atom008Basin
  by_cases h6 : x∈Family.atom006Basin
  · have hn8 : x∉Family.atom008Basin :=
      fun h8 => Set.disjoint_left.mp Family.original_basins_6_8_disjoint h6 h8
    simp [zoneIndex,h6,hn8]
  · by_cases h7 : x∈WholeBandBasin.basin
    · have hn8 : x∉Family.atom008Basin :=
        fun h8 => Set.disjoint_left.mp Family.original_basins_7_8_disjoint h7 h8
      simp [zoneIndex,h6,h7,hn8]
    · by_cases h8 : x∈Family.atom008Basin
      · simp [zoneIndex,h6,h7,h8]
      · by_cases h9 : x∈Family.atom009Basin <;> simp [zoneIndex,h6,h7,h8,h9]

theorem zone_three : zone 3=Family.atom009Basin := by
  classical
  ext x
  change zoneIndex x=3 ↔ x∈Family.atom009Basin
  by_cases h6 : x∈Family.atom006Basin
  · have hn9 : x∉Family.atom009Basin :=
      fun h9 => Set.disjoint_left.mp Family.original_basins_6_9_disjoint h6 h9
    simp [zoneIndex,h6,hn9]
  · by_cases h7 : x∈WholeBandBasin.basin
    · have hn9 : x∉Family.atom009Basin :=
        fun h9 => Set.disjoint_left.mp Family.original_basins_7_9_disjoint h7 h9
      simp [zoneIndex,h6,h7,hn9]
    · by_cases h8 : x∈Family.atom008Basin
      · have hn9 : x∉Family.atom009Basin :=
          fun h9 => Set.disjoint_left.mp Family.original_basins_8_9_disjoint h8 h9
        simp [zoneIndex,h6,h7,h8,hn9]
      · by_cases h9 : x∈Family.atom009Basin <;> simp [zoneIndex,h6,h7,h8,h9]

theorem zone_four : zone 4=residual := by
  classical
  ext x
  change zoneIndex x=4 ↔ x∈residual
  by_cases h6 : x∈Family.atom006Basin
  · simp [zoneIndex,residual,h6]
  · by_cases h7 : x∈WholeBandBasin.basin
    · simp [zoneIndex,residual,h6,h7]
    · by_cases h8 : x∈Family.atom008Basin
      · simp [zoneIndex,residual,h6,h7,h8]
      · by_cases h9 : x∈Family.atom009Basin <;>
          simp [zoneIndex,residual,h6,h7,h8,h9]

theorem pairCells_cover : (⋃ i : Fin 5 × Fin 5, pairCell i)=Set.univ :=
  Partition.Finite.pairCells_cover zoneIndex

theorem pairCells_disjoint : Pairwise (Disjoint on pairCell) :=
  Partition.Finite.pairCells_disjoint zoneIndex

theorem pairCell_measurable (i : Fin 5 × Fin 5) : MeasurableSet (pairCell i) :=
  Partition.Finite.pairCell_measurable zoneIndex zone_measurable i

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
