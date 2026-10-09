import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Spatial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceGaussianModel Set MeasureTheory
noncomputable section

def oldAtomIndex (i : Fin 4) : Fin 13 :=
  if i=0 then 6 else if i=1 then 7 else if i=2 then 8 else 9

theorem old_region_same_source (i : Fin 4) :
    region (some (oldAtomIndex i))=Family.Fifth.zone (Fin.castSucc i) := by
  fin_cases i
  · change region (some 6)=Family.Fifth.zone 0
    rw [original_region,Family.Fifth.zone_zero]
    rfl
  · change region (some 7)=Family.Fifth.zone 1
    rw [original_region,Family.Fifth.zone_one]
    rfl
  · change region (some 8)=Family.Fifth.zone 2
    rw [original_region,Family.Fifth.zone_two]
    rfl
  · change region (some 9)=Family.Fifth.zone 3
    rw [original_region,Family.Fifth.zone_three]
    rfl

theorem old_atomic_cell_same_source (i j : Fin 4) :
    cellEnergy (some (oldAtomIndex i),some (oldAtomIndex j))=
      Family.Fifth.cellEnergy (Fin.castSucc i,Fin.castSucc j) := by
  change Partition.Finite.cellEnergy label
      (some (oldAtomIndex i),some (oldAtomIndex j)) =
    Partition.Finite.cellEnergy Family.Fifth.zoneIndex (Fin.castSucc i,Fin.castSucc j)
  simp only [Partition.Finite.cellEnergy]
  rw [Partition.Finite.pairCell_prod,Partition.Finite.pairCell_prod]
  change (1/2 : ℝ) * ∫ z in
      region (some (oldAtomIndex i)) ×ˢ region (some (oldAtomIndex j)),
        LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.realPairIntegrand z =
    (1/2 : ℝ) * ∫ z in Family.Fifth.zone (Fin.castSucc i) ×ˢ Family.Fifth.zone (Fin.castSucc j),
      LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.realPairIntegrand z
  rw [old_region_same_source i,old_region_same_source j]

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
