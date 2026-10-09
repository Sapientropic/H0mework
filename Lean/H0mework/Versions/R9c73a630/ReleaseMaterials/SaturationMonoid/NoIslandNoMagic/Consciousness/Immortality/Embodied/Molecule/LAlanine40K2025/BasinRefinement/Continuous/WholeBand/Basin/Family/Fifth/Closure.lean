import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Fifth.PairReadback
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
open SourceGaussianModel GlobalSource WholeBandBasin Set MeasureTheory
open WholeBandAttractor
noncomputable section

structure Material where
  parent : Family.Partition.Material
  atom008Basin : Set Point
  energy68 : ℝ
  energy78 : ℝ
  energy89 : ℝ
  residual : Set Point
  cells : Fin 5 × Fin 5 → ℝ

def material : Material where
  parent := Family.Partition.material
  atom008Basin := Family.atom008Basin
  energy68 := Family.interatomicEnergy68
  energy78 := Family.interatomicEnergy78
  energy89 := Family.interatomicEnergy89
  residual := Fifth.residual
  cells := Fifth.cellEnergy

theorem parent_same_source : material.parent=Family.Partition.material := rfl
theorem atom008_basin_same_source : material.atom008Basin=Family.atom008Basin := rfl
theorem cells_same_source (i : Fin 5 × Fin 5) : material.cells i=Fifth.cellEnergy i := rfl

structure Closure : Prop where
  parent : Family.Partition.Closure
  actualAtom008Zero : type_of% Atom008.actual_gradient_zero
  actualAtom008Attraction : type_of% Atom008.actual_convergence
  parentIdentity : type_of% parent_same_source
  basinIdentity : type_of% atom008_basin_same_source
  cellsIdentity : type_of% cells_same_source
  newCover : type_of% Family.atom008_basin_cover
  newOpen : type_of% Family.atom008_basin_open
  newPositive : type_of% Family.atom008_basin_positive
  disjoint68 : type_of% Family.original_basins_6_8_disjoint
  disjoint78 : type_of% Family.original_basins_7_8_disjoint
  disjoint89 : type_of% Family.original_basins_8_9_disjoint
  newInteractions : type_of% Family.three_interatomic_nonnegative ∧
    type_of% Family.three_interatomic_symmetric ∧
    type_of% Family.three_interatomic_patch_limits
  zones : type_of% zone_zero ∧ type_of% zone_one ∧
    type_of% zone_two ∧ type_of% zone_three ∧ type_of% zone_four
  cover : type_of% pairCells_cover
  disjoint : type_of% pairCells_disjoint
  measurable : type_of% pairCell_measurable
  nonnegative : type_of% cell_energy_nonnegative
  symmetric : type_of% cell_energy_symmetric
  fullEnergy : type_of% full_energy_twenty_five_cells
  originalAO : type_of% original_ao_energy_twenty_five_cells
  allPairs : type_of% original_interatomic_6_7 ∧
    type_of% original_interatomic_6_8 ∧
    type_of% original_interatomic_6_9 ∧
    type_of% original_interatomic_7_8 ∧
    type_of% original_interatomic_7_9 ∧
    type_of% original_interatomic_8_9

theorem sourceGeneratedClosure : Closure :=
  ⟨Family.Partition.sourceGeneratedClosure,
    Atom008.actual_gradient_zero,Atom008.actual_convergence,
    parent_same_source,atom008_basin_same_source,cells_same_source,
    Family.atom008_basin_cover,Family.atom008_basin_open,Family.atom008_basin_positive,
    Family.original_basins_6_8_disjoint,Family.original_basins_7_8_disjoint,
    Family.original_basins_8_9_disjoint,
    ⟨Family.three_interatomic_nonnegative,Family.three_interatomic_symmetric,
      Family.three_interatomic_patch_limits⟩,
    ⟨zone_zero,zone_one,zone_two,zone_three,zone_four⟩,
    pairCells_cover,pairCells_disjoint,pairCell_measurable,
    cell_energy_nonnegative,cell_energy_symmetric,
    full_energy_twenty_five_cells,original_ao_energy_twenty_five_cells,
    ⟨original_interatomic_6_7,original_interatomic_6_8,
      original_interatomic_6_9,original_interatomic_7_8,
      original_interatomic_7_9,original_interatomic_8_9⟩⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
