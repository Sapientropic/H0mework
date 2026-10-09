import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Fifth.Energy

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
open SourceGaussianModel GlobalSource Set MeasureTheory
noncomputable section

theorem zone_one_seed : zone 1=Family.basin Family.atom007Seed := by
  rw [zone_one,← Family.atom007_basin_same_source]

private theorem cell_half (i j : Fin 5) (left right : Family.AttractingSeed)
    (hi : zone i=Family.basin left) (hj : zone j=Family.basin right) :
    cellEnergy (i,j)=Family.halfPairEnergy left right := by
  dsimp [cellEnergy,Partition.Finite.cellEnergy]
  rw [Partition.Finite.pairCell_prod]
  change (1/2 : ℝ) * ∫ z in zone i ×ˢ zone j,
    LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.realPairIntegrand z = _
  rw [hi,hj]
  rfl

theorem original_pair_energy (i j : Fin 5) (left right : Family.AttractingSeed)
    (hi : zone i=Family.basin left) (hj : zone j=Family.basin right) :
    cellEnergy (i,j)+cellEnergy (j,i)=Family.interatomicPairEnergy left right := by
  calc
    _ = 2*cellEnergy (i,j) := by rw [← cell_energy_symmetric i j]; ring
    _ = 2*Family.halfPairEnergy left right := by rw [cell_half i j left right hi hj]
    _ = Family.interatomicPairEnergy left right :=
      (Family.interatomic_pair_energy_twice left right).symm

theorem original_interatomic_6_7 :
    cellEnergy (0,1)+cellEnergy (1,0)=Family.interatomicEnergy := by
  have forward : Family.halfPairEnergy Family.atom006Seed Family.atom007Seed =
      Family.crossEnergy := by
    rw [Family.halfPairEnergy,Family.crossEnergy,Family.pairRegion]
    rw [Family.atom007_basin_same_source]
    rfl
  calc
    _ = Family.interatomicPairEnergy Family.atom006Seed Family.atom007Seed :=
      original_pair_energy 0 1 Family.atom006Seed Family.atom007Seed zone_zero zone_one_seed
    _ = 2*Family.crossEnergy := by
      rw [Family.interatomic_pair_energy_twice,forward]
    _ = Family.interatomicEnergy := Family.interatomic_energy_twice.symm

theorem original_interatomic_6_8 :
    cellEnergy (0,2)+cellEnergy (2,0)=Family.interatomicEnergy68 := by
  simpa [Family.interatomicEnergy68] using
    original_pair_energy 0 2 Family.atom006Seed Family.atom008Seed zone_zero zone_two

theorem original_interatomic_6_9 :
    cellEnergy (0,3)+cellEnergy (3,0)=Family.interatomicEnergy69 := by
  simpa [Family.interatomicEnergy69] using
    original_pair_energy 0 3 Family.atom006Seed Family.atom009Seed zone_zero zone_three

theorem original_interatomic_7_8 :
    cellEnergy (1,2)+cellEnergy (2,1)=Family.interatomicEnergy78 := by
  simpa [Family.interatomicEnergy78] using
    original_pair_energy 1 2 Family.atom007Seed Family.atom008Seed zone_one_seed zone_two

theorem original_interatomic_7_9 :
    cellEnergy (1,3)+cellEnergy (3,1)=Family.interatomicEnergy79 := by
  simpa [Family.interatomicEnergy79] using
    original_pair_energy 1 3 Family.atom007Seed Family.atom009Seed zone_one_seed zone_three

theorem original_interatomic_8_9 :
    cellEnergy (2,3)+cellEnergy (3,2)=Family.interatomicEnergy89 := by
  simpa [Family.interatomicEnergy89] using
    original_pair_energy 2 3 Family.atom008Seed Family.atom009Seed zone_two zone_three

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Fifth
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
