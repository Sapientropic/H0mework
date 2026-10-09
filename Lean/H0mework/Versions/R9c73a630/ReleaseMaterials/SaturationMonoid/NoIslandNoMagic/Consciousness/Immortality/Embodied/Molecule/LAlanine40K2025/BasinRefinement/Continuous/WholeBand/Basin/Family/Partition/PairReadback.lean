import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
open SourceGaussianModel WholeBandBasin MeasureTheory
noncomputable section

theorem cell_6_7 : cellEnergy (0,1)=Family.crossEnergy := by
  rw [cellEnergy,original_cell_6_7]
  rfl

theorem cell_6_9 :
    cellEnergy (0,2)=Family.halfPairEnergy Family.atom006Seed Family.atom009Seed := by
  rw [cellEnergy,original_cell_6_9]
  rfl

theorem cell_7_9 :
    cellEnergy (1,2)=Family.halfPairEnergy Family.atom007Seed Family.atom009Seed := by
  rw [cellEnergy,original_cell_7_9]
  rfl

theorem original_interatomic_6_7 :
    cellEnergy (0,1)+cellEnergy (1,0)=Family.interatomicEnergy := by
  calc
    _ = 2*cellEnergy (0,1) := by rw [← cell_energy_symmetric 0 1]; ring
    _ = 2*Family.crossEnergy := by rw [cell_6_7]
    _ = Family.interatomicEnergy := Family.interatomic_energy_twice.symm

theorem original_interatomic_6_9 :
    cellEnergy (0,2)+cellEnergy (2,0)=Family.interatomicEnergy69 := by
  calc
    _ = 2*cellEnergy (0,2) := by rw [← cell_energy_symmetric 0 2]; ring
    _ = 2*Family.halfPairEnergy Family.atom006Seed Family.atom009Seed := by rw [cell_6_9]
    _ = Family.interatomicEnergy69 := by
      exact (Family.interatomic_pair_energy_twice _ _).symm

theorem original_interatomic_7_9 :
    cellEnergy (1,2)+cellEnergy (2,1)=Family.interatomicEnergy79 := by
  calc
    _ = 2*cellEnergy (1,2) := by rw [← cell_energy_symmetric 1 2]; ring
    _ = 2*Family.halfPairEnergy Family.atom007Seed Family.atom009Seed := by rw [cell_7_9]
    _ = Family.interatomicEnergy79 := by
      exact (Family.interatomic_pair_energy_twice _ _).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
